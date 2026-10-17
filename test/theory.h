// The propagator of the external propagation tests (IPASIR-UP, STP
// extension): it holds clauses the solver never sees directly, propagates
// their units with the clause as reason, reports falsified ones, hands some
// over early and rejects models that violate them. It keeps the assignment
// only from the notifications, and every model check compares that with the
// model. See 'propagator.cpp' for what the rounds vary.
#ifndef _theory_h_INCLUDED
#define _theory_h_INCLUDED

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

struct Counts {
  unsigned long notified = 0, repeated = 0, propagations = 0, conflicts = 0,
                eager = 0, checks = 0, rejected = 0, decisions = 0,
                backtracks = 0, shuffled = 0, weakened = 0, duplicated = 0,
                broken = 0, gave_up = 0, terminated = 0, is_decision = 0;
  void add(const Counts &o) {
    notified += o.notified, repeated += o.repeated;
    propagations += o.propagations, conflicts += o.conflicts;
    eager += o.eager, checks += o.checks, rejected += o.rejected;
    decisions += o.decisions, backtracks += o.backtracks;
    shuffled += o.shuffled, weakened += o.weakened;
    duplicated += o.duplicated, broken += o.broken;
    gave_up += o.gave_up, terminated += o.terminated;
    is_decision += o.is_decision;
  }
};

struct Theory {
  unsigned round = 0;
  std::mt19937 *random = nullptr;
  kissat *solver = nullptr;
  std::vector<std::vector<int>> clauses; // hidden
  std::vector<bool> handed;              // given as a permanent clause
  std::vector<bool> observed;            // by variable
  std::vector<signed char> value;        // by variable, from notifications
  std::vector<int> trail;                // variables, in notification order
  std::vector<size_t> levels;            // trail size at each new level
  std::vector<int> reason, pending;
  int reason_for = 0;
  size_t reason_at = 0, pending_at = 0;
  bool propagating = true, deciding = false, advising = false;
  bool checking_only = false; // silent until a model is checked
  bool lazy = false;          // told nothing, only checks models
  bool mangling = false;      // reasons shuffled, weakened, duplicated
  bool giving_up = false;     // rejects some models without a clause
  bool refusing = false;      // gave up on this assignment
  unsigned stop_after = 0;    // kissat_terminate from a callback
  bool gave_up = false, stopped = false; // in the current solve
  Counts counts;

  unsigned pick(unsigned n) { return (*random)() % n; }

  signed char val(int lit) const {
    const signed char v = value[std::abs(lit)];
    return lit < 0 ? -v : v;
  }

  void reset_assignment() {
    std::fill(value.begin(), value.end(), 0);
    trail.clear();
    levels.clear();
    pending.clear();
    pending_at = 0;
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

  void tick() {
    if (stop_after && !--stop_after) {
      kissat_terminate(solver); // allowed from a callback
      stopped = true;
    }
  }

  static void notify_assignment(void *state, const int *lits, size_t size) {
    auto &t = *static_cast<Theory *>(state);
    if (t.lazy)
      fail(t.round, "a lazy propagator was told an assignment");
    t.refusing = false;
    for (size_t i = 0; i < size; i++) {
      const int lit = lits[i], var = std::abs(lit);
      if (!lit || size_t(var) >= t.observed.size() || !t.observed[var])
        fail(t.round, "notified an unobserved variable");
      t.counts.notified++;
      t.counts.is_decision += kissat_is_decision(t.solver, lit);
      const signed char v = lit < 0 ? -1 : 1;
      if (t.value[var]) {
        if (t.value[var] != v)
          fail(t.round, "notified twice with different values");
        t.counts.repeated++;
        continue;
      }
      t.value[var] = v;
      t.trail.push_back(var);
    }
  }
  static void notify_new_decision_level(void *state) {
    auto &t = *static_cast<Theory *>(state);
    if (t.lazy)
      fail(t.round, "a lazy propagator was told a level");
    t.levels.push_back(t.trail.size());
  }
  static void notify_backtrack(void *state, size_t new_level) {
    auto &t = *static_cast<Theory *>(state);
    if (t.lazy)
      fail(t.round, "a lazy propagator was told a backtrack");
    t.counts.backtracks++;
    t.refusing = false;
    if (new_level >= t.levels.size())
      fail(t.round, "backtrack to a level never announced");
    const size_t keep = t.levels[new_level];
    t.levels.resize(new_level);
    while (t.trail.size() > keep) {
      t.value[t.trail.back()] = 0;
      t.trail.pop_back();
    }
    t.pending.clear(); // about the trail just left
    t.tick();
  }
  static int check_found_model(void *state, const int *model, size_t size) {
    auto &t = *static_cast<Theory *>(state);
    t.counts.checks++;
    if (t.lazy) { // knows the assignment only from the model
      t.reset_assignment();
      for (size_t i = 0; i < size; i++)
        t.value[std::abs(model[i])] = model[i] < 0 ? -1 : 1;
    }
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
    t.counts.rejected++;
    if (t.giving_up && t.pick(3) == 0) {
      // Rejected, and no clause: the solve can only end unknown.
      t.counts.gave_up++;
      t.gave_up = t.refusing = true;
      return 0;
    }
    t.stage(t.clauses[i]);
    return 0;
  }
  static int has_external_clause(void *state, int *forgettable) {
    auto &t = *static_cast<Theory *>(state);
    *forgettable = t.pick(2);
    if (!t.pending.empty())
      return 1;
    if (t.checking_only || t.refusing)
      return 0;
    if (t.lazy)
      fail(t.round, "a lazy propagator was asked for a clause unasked");
    int unit = 0;
    int i = t.find(false, unit);
    if (i >= 0) {
      t.counts.conflicts++;
      t.stage(t.clauses[i]);
      return 1;
    }
    if (!t.propagating && (i = t.find(true, unit)) >= 0) {
      t.stage(t.clauses[i]); // a unit of a propagator that does not
      return 1;              // propagate, as a clause
    }
    if (t.pick(64))
      return 0;
    // Now and then a hidden clause early, whatever the trail makes it.
    i = int(t.pick(unsigned(t.clauses.size())));
    if (t.handed[i])
      return 0;
    t.counts.eager++;
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
  void mangle(int unit) {
    switch (pick(10)) {
    case 0: // any order, the propagated literal included
      std::shuffle(reason.begin(), reason.end(), *random);
      counts.shuffled++;
      break;
    case 1: { // weakened by a false literal
      std::vector<int> false_lits;
      for (int var : trail)
        if (std::find(reason.begin(), reason.end(), -val(var) * var) ==
            reason.end())
          false_lits.push_back(-val(var) * var);
      if (false_lits.empty())
        break;
      reason.push_back(false_lits[pick(unsigned(false_lits.size()))]);
      counts.weakened++;
      break;
    }
    case 2: // a literal twice
      reason.push_back(reason[pick(unsigned(reason.size()))]);
      counts.duplicated++;
      break;
    case 3: { // weakened by an open literal: no longer a reason
      if (pick(4))
        break;
      for (size_t v = 1; v < observed.size(); v++)
        if (observed[v] && !value[v] && int(v) != std::abs(unit)) {
          reason.push_back(pick(2) ? int(v) : -int(v));
          counts.broken++;
          break;
        }
      break;
    }
    default:
      break;
    }
  }
  static int propagate(void *state) {
    auto &t = *static_cast<Theory *>(state);
    int unit = 0;
    const int i = t.find(true, unit);
    if (i < 0)
      return 0;
    t.counts.propagations++;
    // The reason: the propagated literal first, then the others.
    t.reason.clear();
    t.reason.push_back(unit);
    for (int lit : t.clauses[i])
      if (lit != unit)
        t.reason.push_back(lit);
    if (t.mangling)
      t.mangle(unit);
    t.reason_for = unit;
    t.reason_at = 0;
    return unit;
  }
  static int add_reason_clause_lit(void *state, int lit) {
    auto &t = *static_cast<Theory *>(state);
    if (t.reason.empty() || t.reason_for != lit)
      fail(t.round, "asked for the reason of another literal");
    if (t.reason_at == t.reason.size())
      return 0;
    return t.reason[t.reason_at++];
  }
  static int decide(void *state) {
    auto &t = *static_cast<Theory *>(state);
    if (t.pick(4))
      return 0;
    std::vector<int> open;
    for (size_t v = 1; v < t.observed.size(); v++)
      if (t.observed[v] && !t.value[v])
        open.push_back(int(v));
    if (open.empty())
      return 0;
    t.counts.decisions++;
    const int var = open[t.pick(unsigned(open.size()))];
    return t.pick(2) ? var : -var;
  }
  static int advise(void *state, int lit) {
    auto &t = *static_cast<Theory *>(state);
    if (t.val(lit))
      fail(t.round, "advice offered for an assigned literal");
    switch (t.pick(3)) {
    case 0:
      return lit;
    case 1:
      return -lit;
    default:
      return 0;
    }
  }

  kissat_external_propagator callbacks() {
    kissat_external_propagator c = {};
    c.state = this;
    c.notify_assignment = notify_assignment;
    c.notify_new_decision_level = notify_new_decision_level;
    c.notify_backtrack = notify_backtrack;
    c.check_found_model = check_found_model;
    c.has_external_clause = has_external_clause;
    c.add_external_clause_lit = add_external_clause_lit;
    if (propagating) {
      c.propagate = propagate;
      c.add_reason_clause_lit = add_reason_clause_lit;
    }
    if (deciding)
      c.decide = decide;
    if (advising)
      c.advise_decision_polarity = advise;
    c.is_lazy = lazy;
    return c;
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

#endif
