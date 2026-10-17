// Simplification without search (STP extension). Random formulas with
// unit chains and equivalences are simplified, and every literal reported
// fixed at the root must be implied (the formula with its negation has no
// model), every literal unit propagation implies must be reported, and the
// answer, when there is one, must match a solver that searched. With the
// incremental option a solve afterwards must answer as the oracle does.
extern "C" {
#include "kissat.h"
}
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>

namespace {

void fail(unsigned round, const char *what) {
  std::fprintf(stderr, "round %u: %s\n", round, what);
  std::exit(1);
}

void add(kissat *solver, const std::vector<int> &clause) {
  for (int lit : clause)
    kissat_add(solver, lit);
  kissat_add(solver, 0);
}

int solve(const std::vector<std::vector<int>> &cnf, int extra) {
  kissat *oracle = kissat_init();
  kissat_set_option(oracle, "quiet", 1);
  for (const auto &clause : cnf)
    add(oracle, clause);
  if (extra)
    add(oracle, {extra});
  const int res = kissat_solve(oracle);
  kissat_release(oracle);
  return res;
}

// The literals unit propagation implies, by variable (0 open), or false
// when it reaches a conflict.
bool propagate(const std::vector<std::vector<int>> &cnf, int vars,
               std::vector<signed char> &value) {
  value.assign(vars + 1, 0);
  for (bool changed = true; changed;) {
    changed = false;
    for (const auto &clause : cnf) {
      int open = 0, unit = 0;
      bool sat = false;
      for (int lit : clause) {
        const signed char v = lit < 0 ? -value[-lit] : value[lit];
        if (v > 0)
          sat = true;
        else if (!v)
          open++, unit = lit;
      }
      if (sat)
        continue;
      if (!open)
        return false;
      if (open == 1) {
        value[std::abs(unit)] = unit < 0 ? -1 : 1;
        changed = true;
      }
    }
  }
  return true;
}

} // namespace

// A fact no clause states and unit propagation cannot reach: 'a' is the
// resolvent of (a | q) and (a | -q), with more clauses around it for a
// lucky assignment to satisfy. Simplification must fix it rather than
// answer with a model.
void check_resolvent() {
  kissat *solver = kissat_init();
  kissat_set_option(solver, "quiet", 1);
  add(solver, {1, 2});
  add(solver, {1, -2});
  for (int v = 3; v < 40; v++)
    add(solver, {-v, v + 1, -1});
  const int res = kissat_simplify(solver);
  if (res == 20 || kissat_root_fixed(solver, 1) != 1)
    fail(0, "the resolvent was not fixed");
  kissat_release(solver);
}

int main(int argc, char **argv) {
  const unsigned rounds = argc > 1 ? std::atoi(argv[1]) : 300;
  check_resolvent();
  std::mt19937 random(20261020);
  unsigned long answers[3] = {0, 0, 0}, fixed = 0, propagated = 0;
  for (unsigned round = 0; round != rounds; ++round) {
    const int vars = 20 + random() % 60;
    auto literal = [&](int var) { return random() % 2 ? var : -var; };
    std::vector<std::vector<int>> cnf;
    for (int i = 0, n = int(vars * (1.5 + (random() % 150) / 100.0)); i != n;
         i++)
      cnf.push_back({literal(1 + random() % vars), literal(1 + random() % vars),
                     literal(1 + random() % vars)});
    // Implication chains from a few units, and some equivalences, so that
    // propagation and probing have something to fix.
    for (int i = 0, n = 1 + random() % 4; i != n; i++)
      cnf.push_back({literal(1 + random() % vars)});
    for (int i = 0, n = random() % (vars / 2); i != n; i++)
      cnf.push_back(
          {-literal(1 + random() % vars), literal(1 + random() % vars)});
    for (int i = 0, n = random() % 6; i != n; i++) {
      const int a = literal(1 + random() % vars);
      const int b = literal(1 + random() % vars);
      cnf.push_back({-a, b});
      cnf.push_back({a, -b});
    }

    const bool incremental = round % 2;
    kissat *solver = kissat_init();
    kissat_set_option(solver, "quiet", 1);
    kissat_set_option(solver, "incremental", incremental);
    kissat_set_option(solver, "factor", (round / 2) % 2);
    kissat_set_option(solver, "preprocess", round % 5 != 4);
    kissat_set_option(solver, "luckyearly", round % 3 == 0); // skipped
    for (const auto &clause : cnf)
      add(solver, clause);
    const int result = kissat_simplify(solver);
    const int expected = solve(cnf, 0);
    answers[result == 10 ? 0 : result == 20 ? 1 : 2]++;
    if (result && result != expected)
      fail(round, "simplification answered differently");
    std::vector<signed char> implied;
    const bool consistent = propagate(cnf, vars, implied);
    if (!consistent && result != 20)
      fail(round, "a propagation conflict was not found");
    if (result != 20) {
      for (int v = 1; v <= vars; v++) {
        const int f = kissat_root_fixed(solver, v);
        if (kissat_root_fixed(solver, -v) != -f)
          fail(round, "a literal and its negation disagree");
        if (implied[v] && f != implied[v])
          fail(round, "a propagated literal was not reported fixed");
        if (!f)
          continue;
        fixed++;
        propagated += implied[v] != 0;
        if (expected == 10 && solve(cnf, f > 0 ? -v : v) != 20)
          fail(round, "a literal reported fixed is not implied");
      }
    }
    if (incremental) {
      const int answer = kissat_solve(solver);
      if (answer != expected)
        fail(round, "a solve after simplification answered differently");
    }
    kissat_release(solver);
  }
  std::printf("rounds %u: simplified to sat %lu, unsat %lu, open %lu; "
              "fixed %lu (by propagation %lu)\n",
              rounds, answers[0], answers[1], answers[2], fixed, propagated);
  return answers[1] && answers[2] && fixed > propagated ? 0 : 1;
}
