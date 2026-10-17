// Clause exchange (STP extension) between copies that each have an
// external propagator (IPASIR-UP, STP extension) connected, as the roots of
// STP's parallel group have on arithmetic. Every copy's propagator holds
// the same hidden clauses, so a clause one copy learned from its own is
// implied for the others too. The copies search in conflict-limited slices
// under shared assumptions and import what the others learned; every answer
// is compared with a solver given all clauses directly, and every model
// checked against them and against what its propagator was told.
#include "theory.h"

namespace {

struct Copy {
  kissat *solver = nullptr;
  Theory theory;
  std::vector<std::vector<int>> learned; // exported, not yet consumed
  std::vector<std::vector<int>> *inbox = nullptr;
  size_t next_clause = 0;
  std::vector<int> buffer;
  unsigned budget = 0;
  unsigned long exported = 0;
};

void learn(void *state, unsigned size, const int *clause) {
  auto *copy = static_cast<Copy *>(state);
  copy->learned.emplace_back(clause, clause + size);
  copy->exported++;
}

unsigned budget(void *state) { return static_cast<Copy *>(state)->budget; }

const int *next(void *state, unsigned *size) {
  auto *copy = static_cast<Copy *>(state);
  if (!copy->inbox || copy->next_clause == copy->inbox->size())
    return nullptr;
  copy->buffer = (*copy->inbox)[copy->next_clause++];
  *size = static_cast<unsigned>(copy->buffer.size());
  return copy->buffer.data();
}

} // namespace

int main(int argc, char **argv) {
  const unsigned rounds = argc > 1 ? std::atoi(argv[1]) : 200;
  std::mt19937 random(20261019);
  kissat_import_statistics total = {0, 0, 0, 0, 0, 0};
  unsigned long exported = 0, answers[3] = {0, 0, 0}, lazy = 0;
  Counts counts;
  for (unsigned round = 0; round != rounds; ++round) {
    const int vars = 40 + random() % 80;
    auto literal = [&](int var) { return random() % 2 ? var : -var; };
    std::vector<bool> observed(vars + 1, false);
    std::vector<int> watched;
    for (int v = 1; v <= vars; v++)
      if ((observed[v] = random() % 3 != 0))
        watched.push_back(v);
    if (watched.size() < 3)
      for (int v = 1; v <= 3; v++)
        if (!observed[v])
          observed[v] = true, watched.push_back(v);
    std::vector<std::vector<int>> base, hidden;
    for (int i = 0, n = int(vars * (3.0 + (random() % 80) / 100.0)); i != n;
         i++)
      base.push_back({literal(1 + random() % vars), literal(1 + random() % vars),
                      literal(1 + random() % vars)});
    for (int i = 0, n = int(vars * (0.3 + (random() % 40) / 100.0)); i != n;
         i++) {
      std::vector<int> clause;
      for (unsigned j = 0, k = 2 + random() % 3; j != k; j++)
        clause.push_back(literal(watched[random() % watched.size()]));
      hidden.push_back(clause);
    }
    std::vector<int> assumptions;
    for (unsigned i = 0, n = random() % 4; i != n; i++)
      assumptions.push_back(literal(1 + random() % vars));

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

    const unsigned copies = 2 + round % 3;
    std::vector<Copy> group(copies);
    std::vector<std::vector<int>> log;
    for (unsigned i = 0; i != copies; ++i) {
      Copy &copy = group[i];
      kissat *solver = copy.solver = kissat_init();
      kissat_set_option(solver, "quiet", 1);
      kissat_set_option(solver, "incremental", 1);
      kissat_set_option(solver, "chrono", round % 2);
      kissat_set_option(solver, "factor", (round / 2) % 2);
      kissat_set_option(solver, "stable", (round / 4) % 3);
      kissat_set_option(solver, "tumble", round % 5 != 0);
      for (const char *name :
           {"reduceinit", "probeinit", "eliminateinit", "rephaseinit"})
        kissat_set_option(solver, name, 10);
      for (const auto &clause : base)
        add(solver, clause);
      if (i)
        kissat_diversify(solver, int(round * 7 + i), int(i % 4) - 1,
                         i % 2 == 0);
      Theory &t = copy.theory;
      t.round = round;
      t.random = &random;
      t.solver = solver;
      t.clauses = hidden;
      t.handed.assign(hidden.size(), false);
      t.observed = observed;
      t.value.assign(vars + 1, 0);
      t.lazy = i == 1 && round % 3 == 1;
      t.propagating = !t.lazy && (round + i) % 4 != 3;
      t.checking_only = t.lazy;
      t.deciding = !t.lazy && (round + i) % 5 == 1;
      t.advising = !t.lazy && (round + i) % 3 == 2;
      t.mangling = (round + i) % 3 == 0;
      lazy += t.lazy;
      const kissat_external_propagator callbacks = t.callbacks();
      kissat_connect_external_propagator(solver, &callbacks);
      for (int v : watched)
        kissat_add_observed_var(solver, v);
      copy.budget = random() % 4;
      copy.inbox = &log;
      kissat_set_learn(solver, &copy, 2 + random() % 7, learn);
      kissat_set_import(solver, &copy, 1 + random() % 4, budget, next);
    }
    auto collect = [&]() {
      for (Copy &other : group) {
        for (auto &clause : other.learned)
          log.push_back(std::move(clause));
        other.learned.clear();
      }
    };
    auto run = [&](Copy &copy) {
      for (int lit : assumptions)
        kissat_assume(copy.solver, lit);
      const int result = kissat_solve(copy.solver);
      if (result && result != expected)
        fail(round, "answer differs from the oracle");
      if (result == 10) {
        if (!satisfies(copy.solver, base) || !satisfies(copy.solver, hidden))
          fail(round, "model violates the formula");
        for (int lit : assumptions)
          if (kissat_value(copy.solver, lit) != lit)
            fail(round, "model violates an assumption");
        if (!copy.theory.lazy)
          for (int v : watched)
            if (copy.theory.value[v] !=
                (kissat_value(copy.solver, v) > 0 ? 1 : -1))
              fail(round, "notified assignment differs from the model");
      }
      collect();
      return result;
    };
    int result = 0;
    for (unsigned slice = 0; !result && slice != 600; ++slice) {
      Copy &copy = group[slice % copies];
      kissat_set_conflict_limit(copy.solver, 20 + random() % 50);
      result = run(copy);
    }
    if (!result)
      result = run(group[0]);
    if (!result)
      fail(round, "no answer without a limit");
    answers[result == 10 ? 0 : 1]++;
    for (Copy &copy : group) {
      kissat_import_statistics s;
      kissat_get_import_statistics(copy.solver, &s);
      total.polls += s.polls, total.clauses += s.clauses;
      total.units += s.units, total.dropped += s.dropped;
      total.satisfied += s.satisfied, total.backtracks += s.backtracks;
      exported += copy.exported;
      counts.add(copy.theory.counts);
      kissat_disconnect_external_propagator(copy.solver);
      kissat_release(copy.solver);
    }
  }
  std::printf("rounds %u: sat %lu unsat %lu (lazy copies %lu)\n", rounds,
              answers[0], answers[1], lazy);
  std::printf("exported %lu, polls %llu, imported %llu (units %llu), "
              "dropped %llu, satisfied %llu, backtracks %llu\n",
              exported, (unsigned long long)total.polls,
              (unsigned long long)total.clauses,
              (unsigned long long)total.units,
              (unsigned long long)total.dropped,
              (unsigned long long)total.satisfied,
              (unsigned long long)total.backtracks);
  std::printf("notified %lu, backtracks %lu, propagations %lu, conflicts "
              "%lu, checks %lu (rejected %lu)\n",
              counts.notified, counts.backtracks, counts.propagations,
              counts.conflicts, counts.checks, counts.rejected);
  // Every path must have been taken: a test that imports nothing proves
  // nothing.
  return answers[0] && answers[1] && lazy && total.clauses && total.units &&
                 total.backtracks && counts.propagations &&
                 counts.conflicts && counts.rejected
             ? 0
             : 1;
}
