// Learned-clause exchange and diversification (STP extension). Copies of
// one formula search in conflict-limited slices and import what the others
// learned; every answer is compared with a fresh solver's and every model
// checked against the formula.
extern "C" {
#include "kissat.h"
}
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>

namespace {

struct Copy {
  kissat *solver = nullptr;
  std::vector<std::vector<int>> learned; // exported, not yet consumed
  std::vector<std::vector<int>> *inbox = nullptr;
  size_t next_clause = 0;
  std::vector<int> buffer;
  int max_var = 0;
  unsigned budget = 0;
  unsigned long exported = 0, budgets = 0;
  bool foreign = false; // an exported literal outside the formula
};

void learn(void *state, unsigned size, const int *clause) {
  auto *copy = static_cast<Copy *>(state);
  std::vector<int> c(clause, clause + size);
  for (int lit : c)
    if (!lit || std::abs(lit) > copy->max_var)
      copy->foreign = true;
  copy->learned.push_back(std::move(c));
  copy->exported++;
}

unsigned budget(void *state) {
  auto *copy = static_cast<Copy *>(state);
  copy->budgets++;
  return copy->budget;
}

const int *next(void *state, unsigned *size) {
  auto *copy = static_cast<Copy *>(state);
  if (!copy->inbox || copy->next_clause == copy->inbox->size())
    return nullptr;
  copy->buffer = (*copy->inbox)[copy->next_clause++];
  *size = static_cast<unsigned>(copy->buffer.size());
  return copy->buffer.data();
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

void fail(unsigned round, const char *what) {
  std::fprintf(stderr, "round %u: %s\n", round, what);
  std::exit(1);
}

} // namespace

int main(int argc, char **argv) {
  const unsigned rounds = argc > 1 ? std::atoi(argv[1]) : 400;
  std::mt19937 random(20261017);
  kissat_import_statistics total = {0, 0, 0, 0, 0, 0};
  unsigned long exported = 0, budgets = 0, answers[3] = {0, 0, 0};
  for (unsigned round = 0; round != rounds; ++round) {
    const int vars = 40 + random() % 80;
    const double ratio = 3.9 + (random() % 80) / 100.0;
    const int width = 3 + (round % 5 == 4);
    std::vector<std::vector<int>> cnf;
    for (int i = 0, n = int(vars * (width == 3 ? ratio : 2 * ratio)); i != n;
         ++i) {
      std::vector<int> clause;
      for (int j = 0; j != width; ++j) {
        const int var = 1 + random() % vars;
        clause.push_back(random() % 2 ? var : -var);
      }
      cnf.push_back(std::move(clause));
    }
    // With 'tumble' off, naming vars + 3 imports vars + 1 and vars + 2
    // without activating them. The last clause, added after the copies are
    // diversified, activates them.
    cnf.push_back({vars + 3, 1 + int(random() % vars)});
    cnf.push_back({vars + 1, -(vars + 2), 1 + int(random() % vars)});
    auto add = [](kissat *solver, const std::vector<int> &clause) {
      for (int lit : clause)
        kissat_add(solver, lit);
      kissat_add(solver, 0);
    };
    auto load = [&](kissat *solver) {
      kissat_set_option(solver, "quiet", 1);
      kissat_set_option(solver, "incremental", round % 2);
      kissat_set_option(solver, "factor", (round / 2) % 2);
      kissat_set_option(solver, "stable", (round / 4) % 3);
      kissat_set_option(solver, "tumble", round % 4 != 0);
      for (const char *name :
           {"reduceinit", "probeinit", "eliminateinit", "rephaseinit"})
        kissat_set_option(solver, name, 10);
      for (size_t i = 0; i + 1 < cnf.size(); i++)
        add(solver, cnf[i]);
    };

    kissat *oracle = kissat_init();
    load(oracle);
    add(oracle, cnf.back());
    const int expected = kissat_solve(oracle);
    if (expected == 10 && !satisfies(oracle, cnf))
      fail(round, "oracle model");
    kissat_release(oracle);

    const unsigned copies = 2 + round % 3;
    std::vector<Copy> group(copies);
    for (unsigned i = 0; i != copies; ++i) {
      Copy &copy = group[i];
      copy.solver = kissat_init();
      copy.max_var = vars + 3;
      copy.budget = random() % 4;
      load(copy.solver);
      if (i)
        kissat_diversify(copy.solver, int(round * 7 + i), int(i % 4) - 1,
                         i % 2 == 0);
      add(copy.solver, cnf.back());
      kissat_set_learn(copy.solver, &copy, 2 + random() % 7, learn);
    }
    // Each copy reads one shared log of every copy's clauses, its own
    // included (an echo is harmless).
    std::vector<std::vector<int>> log;
    for (Copy &copy : group) {
      copy.inbox = &log;
      kissat_set_import(copy.solver, &copy, 1 + random() % 4, budget, next);
    }
    auto collect = [&]() {
      for (Copy &other : group) {
        for (auto &clause : other.learned)
          log.push_back(std::move(clause));
        other.learned.clear();
      }
    };
    auto check = [&](Copy &copy, int result) {
      if (result == 10 && !satisfies(copy.solver, cnf))
        fail(round, "model violates the formula");
      if (result && result != expected)
        fail(round, "answer differs from the oracle");
    };
    int result = 0;
    if (round % 2) {
      // Incremental: conflict-limited slices, round robin, until one
      // decides; then the first copy without a limit.
      for (unsigned slice = 0; !result && slice != 600; ++slice) {
        Copy &copy = group[slice % copies];
        kissat_set_conflict_limit(copy.solver, 20 + random() % 50);
        check(copy, result = kissat_solve(copy.solver));
        collect();
      }
      if (!result)
        check(group[0], result = kissat_solve(group[0].solver));
    } else {
      // One solve call each: every copy imports what the earlier ones
      // learned, from its first poll on.
      for (Copy &copy : group) {
        const int answer = kissat_solve(copy.solver);
        check(copy, answer);
        result = result ? result : answer;
        collect();
      }
    }
    answers[result == 10 ? 0 : result == 20 ? 1 : 2]++;
    for (Copy &copy : group) {
      if (copy.foreign)
        fail(round, "exported a literal outside the formula");
      kissat_import_statistics s;
      kissat_get_import_statistics(copy.solver, &s);
      total.polls += s.polls, total.clauses += s.clauses;
      total.units += s.units, total.dropped += s.dropped;
      total.satisfied += s.satisfied, total.backtracks += s.backtracks;
      exported += copy.exported, budgets += copy.budgets;
      kissat_release(copy.solver);
    }
  }
  std::printf("rounds %u: sat %lu unsat %lu undecided %lu\n", rounds,
              answers[0], answers[1], answers[2]);
  std::printf("exported %lu, polls %llu (budget calls %lu), imported %llu "
              "(units %llu), dropped %llu, satisfied %llu, backtracks %llu\n",
              exported, (unsigned long long)total.polls, budgets,
              (unsigned long long)total.clauses,
              (unsigned long long)total.units,
              (unsigned long long)total.dropped,
              (unsigned long long)total.satisfied,
              (unsigned long long)total.backtracks);
  // Every path must have been taken: a test that imports nothing proves
  // nothing.
  return exported && total.clauses && total.units && total.backtracks &&
                 total.dropped && total.satisfied && budgets
             ? 0
             : 1;
}
