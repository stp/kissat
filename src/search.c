#include "search.h"
#include "incremental.h"
#include "analyze.h"
#include "bump.h"
#include "classify.h"
#include "decide.h"
#include "eliminate.h"
#include "inline.h"
#include "internal.h"
#include "logging.h"
#include "lucky.h"
#include "preprocess.h"
#include "print.h"
#include "probe.h"
#include "propsearch.h"
#include "reduce.h"
#include "reluctant.h"
#include "reorder.h"
#include "rephase.h"
#include "report.h"
#include "restart.h"
#include "terminate.h"
#include "trail.h"
#include "walk.h"

#include <inttypes.h>

static void init_tiers (kissat *solver) {
  for (unsigned stable = 0; stable != 2; stable++) {
    if (!solver->tier1[stable]) {
      assert (!solver->tier2[stable]);
      solver->tier1[stable] = GET_OPTION (tier1);
      solver->tier2[stable] = GET_OPTION (tier2);
      if (solver->tier2[stable] <= solver->tier1[stable])
        solver->tier2[stable] = solver->tier1[stable];
      LOG ("initialized tier1[%u] glue to %u", stable,
           solver->tier1[stable]);
      LOG ("initialized tier2[%u] glue to %u", stable,
           solver->tier2[stable]);
      if (!solver->limits.glue.interval)
        solver->limits.glue.interval = 2;
    }
  }
}

static void start_search (kissat *solver) {
  START (search);
  INC (searches);

  bool stable = GET (searches) == 1 ? (GET_OPTION (stable) == 2)
                                   : solver->saved_stable;

  solver->stable = stable;
  kissat_phase (solver, "search", GET (searches),
                "initializing %s search after %" PRIu64 " conflicts",
                (stable ? "stable" : "focus"), CONFLICTS);

  kissat_init_averages (solver, &AVERAGES);

  kissat_classify (solver);

  if (solver->stable) {
    if (GET (searches) == 1)
      kissat_init_reluctant (solver);
    kissat_update_scores (solver);
  }

  init_tiers (solver);

  if (GET (searches) == 1)
    kissat_init_limits (solver);

  unsigned seed = GET_OPTION (seed);
  if (GET (searches) == 1)
    solver->random = seed;
  LOG ("initialized random number generator with seed %u", seed);

#ifndef QUIET
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  if (!limited->conflicts && !limited->decisions)
    kissat_very_verbose (solver, "starting unlimited search");
  else if (limited->conflicts && !limited->decisions)
    kissat_very_verbose (
        solver, "starting search with conflicts limited to %" PRIu64,
        limits->conflicts);
  else if (!limited->conflicts && limited->decisions)
    kissat_very_verbose (
        solver, "starting search with decisions limited to %" PRIu64,
        limits->decisions);
  else
    kissat_very_verbose (
        solver,
        "starting search with decisions limited to %" PRIu64
        " and conflicts limited to %" PRIu64,
        limits->decisions, limits->conflicts);
  if (stable) {
    START (stable);
    REPORT (0, '[');
  } else {
    START (focused);
    REPORT (0, '{');
  }
#endif
}

static void stop_search (kissat *solver) {
  if (solver->limited.conflicts) {
    LOG ("reset conflict limit");
    solver->limited.conflicts = false;
  }

  if (solver->limited.decisions) {
    LOG ("reset decision limit");
    solver->limited.decisions = false;
  }

  if (solver->termination.flagged) {
    kissat_very_verbose (solver, "termination forced externally");
    solver->termination.flagged = 0;
  }

  solver->saved_stable = solver->stable;
  if (solver->stable) {
    REPORT (0, ']');
    STOP (stable);
    solver->stable = false;
  } else {
    REPORT (0, '}');
    STOP (focused);
  }
  STOP (search);
}

static void report_search_result (kissat *solver, int res) {
#ifndef QUIET
  LOG ("search result %d", res);
  char type = (res == 10 ? '1' : res == 20 ? '0' : '?');
  REPORT (0, type);
#else
  (void) solver, (void) res;
#endif
}

static void iterate (kissat *solver) {
  assert (solver->iterating);
  solver->iterating = false;
  REPORT (0, 'i');
}

static bool conflict_limit_hit (kissat *solver) {
  if (!solver->limited.conflicts)
    return false;
  if (solver->limits.conflicts > solver->statistics.conflicts)
    return false;
  kissat_very_verbose (
      solver, "conflict limit %" PRIu64 " hit after %" PRIu64 " conflicts",
      solver->limits.conflicts, solver->statistics.conflicts);
  return true;
}

static bool decision_limit_hit (kissat *solver) {
  if (!solver->limited.decisions)
    return false;
  if (solver->limits.decisions > solver->statistics.decisions)
    return false;
  kissat_very_verbose (
      solver, "decision limit %" PRIu64 " hit after %" PRIu64 " decisions",
      solver->limits.decisions, solver->statistics.decisions);
  return true;
}

static bool searching (kissat *solver) {
  if (!kissat_propagated (solver))
    return true;
  if (!GET_OPTION (probeinit))
    return true;
  if (!GET_OPTION (eliminateinit))
    return true;
  if (conflict_limit_hit (solver))
    return false;
  return true;
}

static inline bool external_propagating (kissat *solver) {
  return solver->propagator.connected &&
         !solver->propagator.callbacks.is_lazy &&
         SIZE_ARRAY (solver->trail) != solver->propagator.propagated;
}

static inline bool importing (kissat *solver) {
  return solver->exchange.next && CONFLICTS >= solver->exchange.limit;
}

int kissat_search (kissat *solver) {
  REPORT (0, '*');
  int res = 0;
  if (solver->inconsistent)
    res = 20;
  const bool first = !solver->solve_calls;
  const bool assumptions = !EMPTY_STACK (solver->assumptions);
  // Lucky assignments are models no external propagator has checked.
  const bool external = solver->propagator.connected;
  solver->propagator.propagated = INVALID_PROPAGATED;
  if (!res && first && !assumptions && !external && GET_OPTION (luckyearly))
    res = kissat_lucky (solver);
  if (!res && first && kissat_preprocessing (solver))
    res = kissat_preprocess (solver);
  if (!res && first && !assumptions && !external && GET_OPTION (luckylate))
    res = kissat_lucky (solver);
  if (!res)
    kissat_classify (solver);
  if (!res && searching (solver)) {
    start_search (solver);
    const unsigned greedy_mode = GET_OPTION (incrementallucky);
    const uint64_t original_clauses = GET (clauses_original);
    const uint64_t last_greedy = solver->incremental_lucky_last_clauses;
    bool greedy_pending =
        greedy_mode && !external && GET_OPTION (incremental) &&
        !solver->limited.conflicts && !solver->limited.decisions &&
        original_clauses >=
            (unsigned) GET_OPTION (incrementalluckyminclauses) &&
        (!solver->incremental_lucky_failed ||
         (original_clauses >= last_greedy + 100000 &&
          original_clauses / GET_OPTION (incrementalluckygrowth) >=
              last_greedy));
    const uint64_t greedy_conflicts =
        CONFLICTS + GET_OPTION (incrementalluckyinit);
    const uint64_t greedy_decisions =
        DECISIONS + GET_OPTION (incrementalluckydecisions);
    while (!res) {
      clause *conflict = kissat_search_propagate (solver);
      if (conflict)
        res = kissat_analyze (solver, conflict);
      else if (solver->iterating)
        iterate (solver);
      else if (external_propagating (solver)) {
        if (kissat_propagator_propagate (solver) == 20)
          res = 20;
      } else if (kissat_assuming (solver))
        res = kissat_assign_assumption (solver);
      else if (!solver->unassigned) {
        if (!external)
          res = 10;
        else {
          const int checked = kissat_propagator_check_model (solver);
          if (checked < 0)
            break; // rejected without a clause: unknown
          res = checked;
        }
      } else if (TERMINATED (search_terminated_1))
        break;
      else if (importing (solver))
        res = kissat_import_clauses (solver); // shared clauses (STP)
      else if (greedy_pending &&
               solver->unassigned >=
                   (unsigned) GET_OPTION (incrementalluckyminunassigned) &&
               (CONFLICTS >= greedy_conflicts ||
                DECISIONS >= greedy_decisions)) {
        greedy_pending = false;
        solver->incremental_lucky_last_clauses = original_clauses;
        res = kissat_assumption_lucky (solver, greedy_mode);
        solver->incremental_lucky_failed = !res;
      } else if (kissat_reducing (solver))
        res = kissat_reduce (solver);
      else if (kissat_switching_search_mode (solver))
        kissat_switch_search_mode (solver);
      else if (kissat_restarting (solver))
        kissat_restart (solver);
      else if (kissat_reordering (solver))
        kissat_reorder (solver);
      else if (kissat_rephasing (solver))
        kissat_rephase (solver);
      else if (kissat_probing (solver))
        res = kissat_probe (solver);
      else if (kissat_eliminating (solver))
        res = kissat_eliminate (solver);
      else if (conflict_limit_hit (solver))
        break;
      else if (decision_limit_hit (solver))
        break;
      else if (!kissat_propagator_decide (solver))
        kissat_decide (solver);
    }
    stop_search (solver);
  }
  report_search_result (solver, res);
  return res;
}
