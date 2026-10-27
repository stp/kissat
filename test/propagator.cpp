// External propagation (IPASIR-UP, STP extension). A propagator holds
// clauses the solver never sees directly: it propagates their units with
// the clause as reason, reports falsified ones, hands some over early and
// rejects models that violate them. It keeps the assignment only from the
// notifications, and every model check compares that with the model. Every
// answer is compared with a solver given all clauses directly.
//
// Rounds also vary what the CryptoMiniSat fuzzer of the same interface
// varies: lazy propagators, reasons shuffled, weakened by false literals,
// with duplicates or not implying their literal at all, models rejected
// without a clause, searches stopped from a callback or the terminator and
// resumed, and variables observed (fixed ones and after the formula became
// inconsistent included), unobserved and observed again on a reconnected
// propagator between solves. Separate processes check that a callback
// calling into the solver is refused (not on Windows, which has no fork()).
#include "theory.h"

#ifndef _WIN32
#include <csignal>
#include <sys/wait.h>
#include <unistd.h>
#endif

namespace {

struct Terminator {
  unsigned polls = 0;
  bool fired = false;
  static int terminate(void *state) {
    auto &t = *static_cast<Terminator *>(state);
    if (!t.polls)
      return 0;
    if (!--t.polls)
      t.fired = true;
    return t.fired;
  }
};

#ifndef _WIN32

// Whether a callback calling 'call' on the solver is refused (aborts).

struct Intruder {
  kissat *solver;
  void (*call)(kissat *);
  static void notify(void *state, const int *, size_t) {
    auto &i = *static_cast<Intruder *>(state);
    i.call(i.solver);
  }
  static void level(void *) {}
  static void backtrack(void *, size_t) {}
  static int check(void *, const int *, size_t) { return 1; }
  static int clause(void *, int *) { return 0; }
  static int lit(void *) { return 0; }
};

bool refused(void (*call)(kissat *)) {
  std::fflush(stdout);
  std::fflush(stderr);
  const pid_t pid = fork();
  if (pid < 0)
    return false;
  if (!pid) {
    if (!std::freopen("/dev/null", "w", stderr))
      _exit(2);
    kissat *solver = kissat_init();
    kissat_set_option(solver, "quiet", 1);
    kissat_set_option(solver, "incremental", 1);
    add(solver, {1, 2});
    add(solver, {-1, 2});
    Intruder intruder = {solver, call};
    kissat_external_propagator c = {};
    c.state = &intruder;
    c.notify_assignment = Intruder::notify;
    c.notify_new_decision_level = Intruder::level;
    c.notify_backtrack = Intruder::backtrack;
    c.check_found_model = Intruder::check;
    c.has_external_clause = Intruder::clause;
    c.add_external_clause_lit = Intruder::lit;
    kissat_connect_external_propagator(solver, &c);
    kissat_add_observed_var(solver, 1);
    kissat_add_observed_var(solver, 2);
    (void)kissat_solve(solver);
    _exit(0);
  }
  int status = 0;
  if (waitpid(pid, &status, 0) != pid)
    return false;
  return WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT;
}

void check_refusals() {
  if (refused([](kissat *) {}))
    fail(0, "a callback that does not call the solver aborted");
  if (!refused([](kissat *s) { kissat_add(s, 1); }) ||
      !refused([](kissat *s) { (void)kissat_value(s, 1); }) ||
      !refused([](kissat *s) { (void)kissat_solve(s); }) ||
      !refused([](kissat *s) { kissat_add_observed_var(s, 2); }) ||
      !refused([](kissat *s) { kissat_remove_observed_var(s, 1); }) ||
      !refused([](kissat *s) { kissat_disconnect_external_propagator(s); }))
    fail(0, "a callback calling into the solver was not refused");
}

#endif

} // namespace

int main(int argc, char **argv) {
  const unsigned rounds = argc > 1 ? std::atoi(argv[1]) : 300;
#ifndef _WIN32
  check_refusals();
#endif
  std::mt19937 random(20261018);
  unsigned long answers[3] = {0, 0, 0}, solves = 0, lazy_solves = 0;
  unsigned long late = 0, late_fixed = 0, after_unsat = 0, unobserved = 0,
                reconnected = 0;
  Counts total;
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
    auto hidden_clause = [&](int must) {
      std::vector<int> clause;
      if (must)
        clause.push_back(literal(must));
      for (unsigned j = clause.size(), k = 2 + random() % 3; j < k; j++)
        clause.push_back(literal(watched[random() % watched.size()]));
      return clause;
    };
    if (watched.size() > 2)
      for (int i = 0, n = int(vars * (0.4 + (random() % 40) / 100.0)); i != n;
           i++)
        hidden.push_back(hidden_clause(0));
    if (watched.empty()) {
      observed[1] = true;
      watched.push_back(1);
    }
    if (hidden.empty())
      hidden.push_back({literal(watched[0])});

    kissat *solver = kissat_init();
    Theory theory;
    theory.round = round;
    theory.random = &random;
    theory.solver = solver;
    theory.clauses = hidden;
    theory.handed.assign(hidden.size(), false);
    theory.observed = observed;
    theory.value.assign(vars + 1, 0);
    theory.lazy = round % 9 == 4;
    theory.propagating = !theory.lazy && round % 4 != 3;
    theory.checking_only = theory.lazy || round % 8 == 7;
    theory.deciding = !theory.lazy && round % 5 == 1;
    theory.advising = !theory.lazy && round % 3 == 2;
    theory.mangling = round % 3 == 0;
    theory.giving_up = round % 10 == 3;
    const bool changing = round % 2; // observations change between solves

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
    Terminator terminator;
    kissat_set_terminate(solver, &terminator, Terminator::terminate);
    kissat_external_propagator callbacks = theory.callbacks();
    kissat_connect_external_propagator(solver, &callbacks);
    for (int v : watched)
      kissat_add_observed_var(solver, v);

    for (unsigned step = 0, steps = 1 + random() % 6; step != steps; step++) {
      if (step && changing) {
        if (random() % 6 == 0) {
          // Reconnected: told everything again from the root.
          kissat_disconnect_external_propagator(solver);
          theory.reset_assignment();
          kissat_connect_external_propagator(solver, &callbacks);
          for (int v : watched)
            kissat_add_observed_var(solver, v);
          reconnected++;
        }
        if (watched.size() > 2 && random() % 4 == 0) {
          // Unobserved: its hidden clauses become ordinary ones.
          const size_t at = random() % watched.size();
          const int var = watched[at];
          for (size_t i = 0; i < theory.clauses.size();) {
            const auto &clause = theory.clauses[i];
            if (std::find_if(clause.begin(), clause.end(), [&](int lit) {
                  return std::abs(lit) == var;
                }) == clause.end()) {
              i++;
              continue;
            }
            base.push_back(clause);
            add(solver, clause);
            theory.clauses.erase(theory.clauses.begin() + i);
            theory.handed.erase(theory.handed.begin() + i);
          }
          kissat_remove_observed_var(solver, var);
          theory.observed[var] = false;
          watched.erase(watched.begin() + at);
          unobserved++;
          if (theory.clauses.empty()) {
            theory.clauses.push_back({literal(watched[0])});
            theory.handed.push_back(false);
          }
        }
        if (random() % 3 == 0) {
          // Observed late, perhaps fixed already or after the formula
          // became inconsistent, with hidden clauses of its own.
          std::vector<int> open;
          for (int v = 1; v <= vars; v++)
            if (!theory.observed[v])
              open.push_back(v);
          if (!open.empty()) {
            const int var = open[random() % open.size()];
            if (random() % 2) {
              // Fixed first, told as a root assignment of its own.
              const int unit = literal(var);
              base.push_back({unit});
              add(solver, {unit});
              late_fixed++;
            }
            if (kissat_inconsistent(solver))
              after_unsat++;
            kissat_add_observed_var(solver, var);
            theory.observed[var] = true;
            watched.push_back(var);
            late++;
            for (unsigned i = 0, n = 1 + random() % 2; i != n; i++) {
              theory.clauses.push_back(hidden_clause(var));
              theory.handed.push_back(false);
            }
          }
        }
        if (random() % 2) {
          // A permanent clause between solves.
          std::vector<int> clause = {literal(1 + random() % vars),
                                     literal(1 + random() % vars),
                                     literal(1 + random() % vars)};
          base.push_back(clause);
          add(solver, clause);
        }
      }
      std::vector<int> assumptions;
      for (unsigned i = 0, n = random() % 4; i != n; i++)
        assumptions.push_back(literal(1 + random() % vars));
      kissat *oracle = kissat_init();
      kissat_set_option(oracle, "quiet", 1);
      for (const auto &clause : base)
        add(oracle, clause);
      for (const auto &clause : theory.clauses)
        add(oracle, clause);
      for (int lit : assumptions)
        add(oracle, {lit});
      const int expected = kissat_solve(oracle);
      kissat_release(oracle);

      theory.gave_up = theory.stopped = theory.refusing = false;
      terminator.fired = false;
      terminator.polls = 0;
      theory.stop_after = 0;
      switch (round % 11) {
      case 5:
        terminator.polls = 1 + random() % 50;
        break;
      case 6:
        if (!theory.lazy)
          theory.stop_after = 1 + random() % 20;
        break;
      default:
        break;
      }
      for (int lit : assumptions)
        kissat_assume(solver, lit);
      const int result = kissat_solve(solver);
      theory.stop_after = 0; // not between solves
      solves++;
      lazy_solves += theory.lazy;
      const bool stopped = terminator.fired || theory.stopped;
      theory.counts.terminated += stopped;
      if (!result) {
        if (!stopped && !theory.gave_up)
          fail(round, "unknown without a reason");
      } else if (result != expected)
        fail(round, "answer differs from the oracle");
      if (result == 10) {
        if (!satisfies(solver, base) || !satisfies(solver, theory.clauses))
          fail(round, "model violates the formula");
        for (int lit : assumptions)
          if (kissat_value(solver, lit) != lit)
            fail(round, "model violates an assumption");
        if (!theory.lazy)
          for (int v : watched)
            if (theory.value[v] != (kissat_value(solver, v) > 0 ? 1 : -1))
              fail(round, "notified assignment differs from the model");
      }
      answers[result == 10 ? 0 : result == 20 ? 1 : 2]++;
    }
    kissat_disconnect_external_propagator(solver);
    kissat_release(solver);
    total.add(theory.counts);
  }
  std::printf("rounds %u, solves %lu (lazy %lu): sat %lu unsat %lu unknown "
              "%lu\n",
              rounds, solves, lazy_solves, answers[0], answers[1],
              answers[2]);
  std::printf("notified %lu (repeated %lu, decisions %lu), backtracks %lu, "
              "propagations %lu, conflicts %lu, eager %lu, checks %lu "
              "(rejected %lu, without a clause %lu), decisions %lu\n",
              total.notified, total.repeated, total.is_decision,
              total.backtracks, total.propagations, total.conflicts,
              total.eager, total.checks, total.rejected, total.gave_up,
              total.decisions);
  std::printf("reasons shuffled %lu, weakened %lu, duplicated %lu, broken "
              "%lu; stopped %lu; observed late %lu (fixed %lu, after unsat "
              "%lu), unobserved %lu, reconnected %lu\n",
              total.shuffled, total.weakened, total.duplicated, total.broken,
              total.terminated, late, late_fixed, after_unsat, unobserved,
              reconnected);
  const bool covered =
      answers[0] && answers[1] && lazy_solves && total.propagations &&
      total.conflicts && total.rejected && total.decisions && total.eager &&
      total.shuffled && total.weakened && total.duplicated && total.broken &&
      total.gave_up && total.terminated && total.is_decision && late &&
      late_fixed && after_unsat && unobserved && reconnected;
  return covered ? 0 : 1;
}
