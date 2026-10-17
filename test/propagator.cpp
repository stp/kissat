// External propagation (IPASIR-UP, STP extension). A propagator holds
// clauses the solver never sees directly: it propagates their units with
// the clause as reason, reports falsified ones, hands some over early and
// rejects models that violate them. It keeps the assignment only from the
// notifications, and every model check compares that with the model. Every
// answer is compared with a solver given all clauses directly.
extern "C" {
#include "kissat.h"
}
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>

namespace {

void fail(unsigned round, const char *what) {
  std::fprintf(stderr, "round %u: %s\n", round, what);
  std::exit(1);
}

struct Theory {
  unsigned round = 0;
  std::mt19937 *random = nullptr;
  std::vector<std::vector<int>> clauses; // hidden
  std::vector<bool> handed;              // given as a permanent clause
  std::vector<bool> observed;            // by variable
  std::vector<signed char> value;        // by variable, from notifications
  std::vector<int> trail;                // variables, in notification order
  std::vector<size_t> levels;            // trail size at each new level
  std::vector<int> reason, pending;
  size_t reason_at = 0, pending_at = 0;
  bool propagating = true, deciding = false, advising = false;
  bool checking_only = false; // silent until a model is checked
  unsigned long notified = 0, repeated = 0, propagations = 0, conflicts = 0,
                eager = 0, checks = 0, rejected = 0, decisions = 0,
                backtracks = 0;

  signed char val(int lit) const {
    const signed char v = value[std::abs(lit)];
    return lit < 0 ? -v : v;
  }

  // A hidden clause falsified, or unit, under the notified assignment.
  int find(bool want_unit, int &unit) const {
    for (size_t i = 0; i < clauses.size(); i++) {
      int open = 0, last = 0;
      bool sat = false;
      for (int lit : clauses[i]) {
        const signed char v = val(lit);
        if (v > 0) {
          sat = true;
          break;
        }
        if (!v)
          open++, last = lit;
      }
      if (sat)
        continue;
      if (!open && !want_unit)
        return int(i);
      if (open == 1 && want_unit) {
        unit = last;
        return int(i);
      }
    }
    return -1;
  }

  void stage(const std::vector<int> &clause) {
    pending = clause;
    pending_at = 0;
  }

  static void notify_assignment(void *state, const int *lits, size_t size) {
    auto &t = *static_cast<Theory *>(state);
    for (size_t i = 0; i < size; i++) {
      const int lit = lits[i], var = std::abs(lit);
      if (!lit || size_t(var) >= t.observed.size() || !t.observed[var])
        fail(t.round, "notified an unobserved variable");
      t.notified++;
      const signed char v = lit < 0 ? -1 : 1;
      if (t.value[var]) {
        if (t.value[var] != v)
          fail(t.round, "notified twice with different values");
        t.repeated++;
        continue;
      }
      t.value[var] = v;
      t.trail.push_back(var);
    }
  }
  static void notify_new_decision_level(void *state) {
    auto &t = *static_cast<Theory *>(state);
    t.levels.push_back(t.trail.size());
  }
  static void notify_backtrack(void *state, size_t new_level) {
    auto &t = *static_cast<Theory *>(state);
    t.backtracks++;
    if (new_level >= t.levels.size())
      fail(t.round, "backtrack to a level never announced");
    const size_t keep = t.levels[new_level];
    t.levels.resize(new_level);
    while (t.trail.size() > keep) {
      t.value[t.trail.back()] = 0;
      t.trail.pop_back();
    }
    t.pending.clear(); // about the trail just left
  }
  static int check_found_model(void *state, const int *model, size_t size) {
    auto &t = *static_cast<Theory *>(state);
    t.checks++;
    size_t observed = 0;
    for (size_t i = 0; i < size; i++) {
      const int lit = model[i];
      if (t.val(lit) <= 0)
        fail(t.round, "model differs from the notified assignment");
    }
    for (size_t v = 1; v < t.observed.size(); v++)
      observed += t.observed[v];
    if (observed != size)
      fail(t.round, "model does not cover the observed variables");
    int unit = 0;
    const int i = t.find(false, unit);
    if (i < 0)
      return 1;
    t.rejected++;
    t.stage(t.clauses[i]);
    return 0;
  }
  static int has_external_clause(void *state, int *forgettable) {
    auto &t = *static_cast<Theory *>(state);
    *forgettable = (*t.random)() % 2;
    if (!t.pending.empty())
      return 1;
    if (t.checking_only)
      return 0;
    int unit = 0;
    int i = t.find(false, unit);
    if (i >= 0) {
      t.conflicts++;
      t.stage(t.clauses[i]);
      return 1;
    }
    if (!t.propagating && (i = t.find(true, unit)) >= 0) {
      t.stage(t.clauses[i]); // a lazy propagator's unit, as a clause
      return 1;
    }
    if ((*t.random)() % 64)
      return 0;
    // Now and then a hidden clause early, whatever the trail makes it.
    i = int((*t.random)() % t.clauses.size());
    if (t.handed[i])
      return 0;
    t.eager++;
    if (!*forgettable)
      t.handed[i] = true;
    t.stage(t.clauses[i]);
    return 1;
  }
  static int add_external_clause_lit(void *state) {
    auto &t = *static_cast<Theory *>(state);
    if (t.pending_at == t.pending.size()) {
      t.pending.clear();
      t.pending_at = 0;
      return 0;
    }
    return t.pending[t.pending_at++];
  }
  static int propagate(void *state) {
    auto &t = *static_cast<Theory *>(state);
    int unit = 0;
    const int i = t.find(true, unit);
    if (i < 0)
      return 0;
    t.propagations++;
    // The reason: the propagated literal first, then the others.
    t.reason.clear();
    t.reason.push_back(unit);
    for (int lit : t.clauses[i])
      if (lit != unit)
        t.reason.push_back(lit);
    t.reason_at = 0;
    return unit;
  }
  static int add_reason_clause_lit(void *state, int lit) {
    auto &t = *static_cast<Theory *>(state);
    if (t.reason.empty() || t.reason[0] != lit)
      fail(t.round, "asked for the reason of another literal");
    if (t.reason_at == t.reason.size())
      return 0;
    return t.reason[t.reason_at++];
  }
  static int decide(void *state) {
    auto &t = *static_cast<Theory *>(state);
    if ((*t.random)() % 4)
      return 0;
    std::vector<int> open;
    for (size_t v = 1; v < t.observed.size(); v++)
      if (t.observed[v] && !t.value[v])
        open.push_back(int(v));
    if (open.empty())
      return 0;
    t.decisions++;
    const int var = open[(*t.random)() % open.size()];
    return (*t.random)() % 2 ? var : -var;
  }
  static int advise(void *state, int lit) {
    auto &t = *static_cast<Theory *>(state);
    if (t.val(lit))
      fail(t.round, "advice offered for an assigned literal");
    switch ((*t.random)() % 3) {
    case 0:
      return lit;
    case 1:
      return -lit;
    default:
      return 0;
    }
  }
};

void add(kissat *solver, const std::vector<int> &clause) {
  for (int lit : clause)
    kissat_add(solver, lit);
  kissat_add(solver, 0);
}

bool satisfies(kissat *solver, const std::vector<std::vector<int>> &cnf) {
  for (const auto &clause : cnf) {
    bool sat = false;
    for (int lit : clause)
      sat = sat || kissat_value(solver, lit) == lit;
    if (!sat)
      return false;
  }
  return true;
}

} // namespace

int main(int argc, char **argv) {
  const unsigned rounds = argc > 1 ? std::atoi(argv[1]) : 300;
  std::mt19937 random(20261018);
  unsigned long answers[3] = {0, 0, 0}, solves = 0;
  Theory total;
  for (unsigned round = 0; round != rounds; ++round) {
    const int vars = 30 + random() % 60;
    std::vector<std::vector<int>> base, hidden;
    auto literal = [&](int var) { return random() % 2 ? var : -var; };
    std::vector<bool> observed(vars + 1, false);
    for (int v = 1; v <= vars; v++)
      observed[v] = random() % 3 != 0;
    std::vector<int> watched;
    for (int v = 1; v <= vars; v++)
      if (observed[v])
        watched.push_back(v);
    for (int i = 0, n = int(vars * (3.2 + (random() % 60) / 100.0)); i != n;
         i++)
      base.push_back({literal(1 + random() % vars), literal(1 + random() % vars),
                      literal(1 + random() % vars)});
    if (watched.size() > 2)
      for (int i = 0, n = int(vars * (0.4 + (random() % 40) / 100.0)); i != n;
           i++) {
        std::vector<int> clause;
        for (unsigned j = 0, k = 2 + random() % 3; j != k; j++)
          clause.push_back(literal(watched[random() % watched.size()]));
        hidden.push_back(clause);
      }
    if (hidden.empty())
      hidden.push_back({literal(watched.empty() ? 1 : watched[0])});

    Theory theory;
    theory.round = round;
    theory.random = &random;
    theory.clauses = hidden;
    theory.handed.assign(hidden.size(), false);
    theory.observed = observed;
    theory.value.assign(vars + 1, 0);
    theory.propagating = round % 4 != 3;
    theory.checking_only = round % 8 == 7;
    theory.deciding = round % 5 == 1;
    theory.advising = round % 3 == 2;

    kissat *solver = kissat_init();
    kissat_set_option(solver, "quiet", 1);
    kissat_set_option(solver, "incremental", 1);
    kissat_set_option(solver, "chrono", round % 2);
    kissat_set_option(solver, "stable", (round / 2) % 3);
    kissat_set_option(solver, "incrementalreuse", (round / 6) % 3);
    kissat_set_option(solver, "factor", (round / 3) % 2);
    kissat_set_option(solver, "tumble", round % 7 != 0);
    for (const char *name :
         {"reduceinit", "probeinit", "eliminateinit", "rephaseinit"})
      kissat_set_option(solver, name, 10 + random() % 40);
    for (const auto &clause : base)
      add(solver, clause);
    kissat_external_propagator callbacks = {};
    callbacks.state = &theory;
    callbacks.notify_assignment = Theory::notify_assignment;
    callbacks.notify_new_decision_level = Theory::notify_new_decision_level;
    callbacks.notify_backtrack = Theory::notify_backtrack;
    callbacks.check_found_model = Theory::check_found_model;
    callbacks.has_external_clause = Theory::has_external_clause;
    callbacks.add_external_clause_lit = Theory::add_external_clause_lit;
    if (theory.propagating) {
      callbacks.propagate = Theory::propagate;
      callbacks.add_reason_clause_lit = Theory::add_reason_clause_lit;
    }
    if (theory.deciding)
      callbacks.decide = Theory::decide;
    if (theory.advising)
      callbacks.advise_decision_polarity = Theory::advise;
    kissat_connect_external_propagator(solver, &callbacks);
    for (int v : watched)
      kissat_add_observed_var(solver, v);

    for (unsigned step = 0, steps = 1 + random() % 4; step != steps; step++) {
      std::vector<int> assumptions;
      for (unsigned i = 0, n = random() % 4; i != n; i++)
        assumptions.push_back(literal(1 + random() % vars));
      if (step && random() % 2) {
        // A permanent clause between solves.
        std::vector<int> clause = {literal(1 + random() % vars),
                                   literal(1 + random() % vars),
                                   literal(1 + random() % vars)};
        base.push_back(clause);
        add(solver, clause);
      }
      kissat *oracle = kissat_init();
      kissat_set_option(oracle, "quiet", 1);
      for (const auto &clause : base)
        add(oracle, clause);
      for (const auto &clause : hidden)
        add(oracle, clause);
      for (int lit : assumptions)
        add(oracle, {lit});
      const int expected = kissat_solve(oracle);
      kissat_release(oracle);

      for (int lit : assumptions)
        kissat_assume(solver, lit);
      const int result = kissat_solve(solver);
      solves++;
      if (result != expected)
        fail(round, "answer differs from the oracle");
      if (result == 10) {
        if (!satisfies(solver, base) || !satisfies(solver, hidden))
          fail(round, "model violates the formula");
        for (int lit : assumptions)
          if (kissat_value(solver, lit) != lit)
            fail(round, "model violates an assumption");
        for (int v : watched)
          if (theory.value[v] != (kissat_value(solver, v) > 0 ? 1 : -1))
            fail(round, "notified assignment differs from the model");
      }
      answers[result == 10 ? 0 : result == 20 ? 1 : 2]++;
    }
    kissat_disconnect_external_propagator(solver);
    kissat_release(solver);
    total.notified += theory.notified, total.repeated += theory.repeated;
    total.propagations += theory.propagations;
    total.conflicts += theory.conflicts, total.eager += theory.eager;
    total.checks += theory.checks, total.rejected += theory.rejected;
    total.decisions += theory.decisions;
    total.backtracks += theory.backtracks;
  }
  std::printf("rounds %u, solves %lu: sat %lu unsat %lu unknown %lu\n",
              rounds, solves, answers[0], answers[1], answers[2]);
  std::printf("notified %lu (repeated %lu), backtracks %lu, propagations "
              "%lu, conflicts %lu, eager %lu, checks %lu (rejected %lu), "
              "decisions %lu\n",
              total.notified, total.repeated, total.backtracks,
              total.propagations, total.conflicts, total.eager, total.checks,
              total.rejected, total.decisions);
  return answers[0] && answers[1] && !answers[2] && total.propagations &&
                 total.conflicts && total.rejected && total.decisions &&
                 total.eager
             ? 0
             : 1;
}
