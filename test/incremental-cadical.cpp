// Optional larger incremental oracle check. Link libkissat and libcadical.
#include <cadical/cadical.hpp>
extern "C" {
#include "kissat.h"
}
#include <algorithm>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>

int main() {
  std::mt19937 random(20261013);
  unsigned solves = 0;
  for (unsigned session = 0; session != 300; ++session) {
    kissat *solver = kissat_init();
    CaDiCaL::Solver oracle;
    oracle.set("quiet", 1);
    kissat_set_option(solver, "quiet", 1);
    kissat_set_option(solver, "incremental", 1);
    kissat_set_option(solver, "incrementalreuse", session % 3);
    kissat_set_option(solver, "stable", (session / 3) % 3);
    kissat_set_option(solver, "factor", session % 2);
    for (const char *name : {"reduceinit", "probeinit", "eliminateinit", "rephaseinit", "rephaseint"})
      kissat_set_option(solver, name, 10);
    std::vector<int> variables;
    std::vector<bool> planted(1, false);
    auto fresh = [&]() {
      int id = std::max(variables.empty() ? 0 : variables.back(),
                        kissat_maximum_variable(solver)) + 1;
      variables.push_back(id);
      if (planted.size() <= static_cast<size_t>(id)) planted.resize(id + 1);
      planted[id] = random() % 2;
      kissat_reserve(solver, id);
      return id;
    };
    auto literal = [&]() {
      int id = variables[random() % variables.size()];
      return random() % 2 ? id : -id;
    };
    auto truth = [](int lit, const std::vector<bool>& values) {
      return values[std::abs(lit)] == (lit > 0);
    };
    std::vector<std::vector<int>> clauses;
    auto add = [&](std::vector<int> clause) {
      if (!std::any_of(clause.begin(), clause.end(), [&](int lit) { return truth(lit, planted); }))
        clause[0] = -clause[0];
      for (int lit : clause) { kissat_add(solver, lit); oracle.add(lit); }
      kissat_add(solver, 0); oracle.add(0);
      clauses.push_back(std::move(clause));
    };
    for (unsigned i = 0, n = 40 + random() % 100; i != n; ++i) fresh();
    for (unsigned i = 0, n = variables.size() * 5; i != n; ++i)
      add({literal(), literal(), literal()});
    std::vector<int> assumptions;
    for (unsigned step = 0; step != 80; ++step) {
      if (step % 7 == 0) { fresh(); add({literal(), literal()}); }
      if (step % 3 == 0) add({literal(), literal(), literal()});
      if (!assumptions.empty() && random() % 2) assumptions.pop_back();
      if (assumptions.size() < 10 && random() % 3) assumptions.push_back(literal());
      if (step % 13 == 0) assumptions.clear();
      for (int lit : assumptions) { kissat_assume(solver, lit); oracle.assume(lit); }
      if (step % 11 == 0) kissat_set_conflict_limit(solver, 0);
      int result = kissat_solve(solver);
      if (!result) {
        for (int lit : assumptions) kissat_assume(solver, lit);
        result = kissat_solve(solver);
      }
      int expected = oracle.solve();
      ++solves;
      if (result != expected) {
        std::fprintf(stderr, "Mismatch session=%u step=%u kissat=%d cadical=%d\n",
                     session, step, result, expected);
        return 1;
      }
      if (result == 10) {
        std::vector<bool> values(planted.size());
        for (int var : variables) values[var] = kissat_value(solver, var) > 0;
        for (const auto& clause : clauses)
          assert(std::any_of(clause.begin(), clause.end(), [&](int lit) { return truth(lit, values); }));
        for (int lit : assumptions) assert(truth(lit, values));
      } else {
        for (int lit : assumptions)
          if (kissat_failed(solver, lit)) oracle.assume(lit);
        assert(oracle.solve() == 20);
      }
      assert(!kissat_inconsistent(solver));
    }
    if (std::getenv("KISSAT_STRESS_STATISTICS")) {
      kissat_set_option(solver, "quiet", 0);
      kissat_set_option(solver, "statistics", 1);
      kissat_print_statistics(solver);
    }
    kissat_release(solver);
  }
  std::printf("PASS: 300 larger sessions, %u CaDiCaL differential solves, models and cores\n", solves);
}
