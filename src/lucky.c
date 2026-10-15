#include "lucky.h"
#include "analyze.h"
#include "backtrack.h"
#include "decide.h"
#include "inline.h"
#include "internal.h"
#include "print.h"
#include "proprobe.h"
#include "report.h"
#include "resources.h"
#include "terminate.h"

static int assumption_walk (kissat *solver, unsigned base, bool reverse,
                            bool positive, double deadline) {
  const size_t size = SIZE_STACK (solver->import);
  for (size_t offset = 1; offset < size; offset++) {
    if (!(offset & 1023) && (TERMINATED (lucky_terminated_1) ||
                             kissat_wall_clock_time () >= deadline))
      return 0;
    const size_t position = reverse ? size - offset : offset;
    const import *import = &PEEK_STACK (solver->import, position);
    if (!import->imported || import->eliminated)
      continue;
    unsigned lit = import->lit;
    if (!ACTIVE (IDX (lit)) || VALUE (lit))
      continue;
    if (!positive)
      lit = NOT (lit);
    kissat_internal_assume (solver, lit);
    clause *conflict = kissat_probing_propagate (solver, 0, true);
    if (!conflict)
      continue;
    INC (incremental_lucky_conflicts);
    assert (solver->level > base);
    if (solver->level <= base)
      return 0;
    kissat_backtrack_without_updating_phases (solver, solver->level - 1);
    kissat_internal_assume (solver, NOT (lit));
    conflict = kissat_probing_propagate (solver, 0, true);
    if (conflict) {
      INC (incremental_lucky_conflicts);
      return 0;
    }
  }
  return solver->unassigned ? 0 : 10;
}

int kissat_assumption_lucky (kissat *solver, unsigned mode) {
  assert (GET_OPTION (incremental));
  assert (mode >= 1 && mode <= 3);
  assert (!solver->probing);
  assert (kissat_propagated (solver));
  const unsigned base =
      (unsigned) SIZE_STACK (solver->assumption_decisions);
  assert (base <= solver->level);
  kissat_backtrack_in_consistent_state (solver, base);
  INC (incremental_lucky_attempts);
  if (mode == 3)
    return 0;
  const double deadline = kissat_wall_clock_time () +
                          0.001 * GET_OPTION (incrementalluckymilliseconds);
  START (lucky);
  // Assumptions stay on their decision levels. A failed greedy branch must
  // not learn the root units that the ordinary assumption-free lucky walk
  // can learn, so unsuccessful walks only restore this prefix.
  solver->probing = true;
  int result = 0;
  const unsigned rounds = mode == 2 ? 4 : 1;
  for (unsigned round = 0; round < rounds && !result; round++) {
    if (TERMINATED (lucky_terminated_1) ||
        kissat_wall_clock_time () >= deadline)
      break;
    result = assumption_walk (solver, base, round >= 2, (round & 1) != 0,
                              deadline);
    if (!result)
      kissat_backtrack_without_updating_phases (solver, base);
  }
  solver->probing = false;
  STOP (lucky);
  if (result) {
    assert (kissat_propagated (solver));
    assert (!solver->unassigned);
    INC (incremental_lucky_successes);
  } else if (kissat_wall_clock_time () >= deadline)
    INC (incremental_lucky_timeouts);
  return result;
}

static bool no_all_negative_clauses (struct kissat *solver) {
  clause *last_irredundant = kissat_last_irredundant_clause (solver);
  for (all_clauses (c)) {
    if (TERMINATED (lucky_terminated_1))
      return false;
    if (last_irredundant && last_irredundant < c)
      break;
    if (c->redundant)
      continue;
    if (c->garbage)
      continue;
    for (all_literals_in_clause (lit, c))
      if (!NEGATED (lit) && VALUE (lit) >= 0)
        goto CONTINUE_WITH_NEXT_CLAUSE;
    kissat_verbose (solver, "found all negative large clause");
    return false;
  CONTINUE_WITH_NEXT_CLAUSE:;
  }
  assert (solver->watching);
  for (all_variables (idx)) {
    if (TERMINATED (lucky_terminated_1))
      return false;
    if (!ACTIVE (idx))
      continue;
    const unsigned lit = LIT (idx);
    const unsigned not_lit = NOT (lit);
    for (all_binary_blocking_watches (watch, WATCHES (not_lit))) {
      if (!watch.type.binary)
        continue;
      const unsigned other = watch.binary.lit;
      if (NEGATED (other) && ACTIVE (IDX (other))) {
        kissat_verbose (solver, "found all negative binary clause");
        return false;
      }
    }
  }
  kissat_message (solver, "lucky no all-negative clause");
  return true;
}

static bool no_all_positive_clauses (struct kissat *solver) {
  clause *last_irredundant = kissat_last_irredundant_clause (solver);
  for (all_clauses (c)) {
    if (TERMINATED (lucky_terminated_1))
      return false;
    if (last_irredundant && last_irredundant < c)
      break;
    if (c->redundant)
      continue;
    if (c->garbage)
      continue;
    for (all_literals_in_clause (lit, c))
      if (NEGATED (lit) && VALUE (lit) >= 0)
        goto CONTINUE_WITH_NEXT_CLAUSE;
    kissat_verbose (solver, "found all positive large clause");
    return false;
  CONTINUE_WITH_NEXT_CLAUSE:;
  }
  assert (solver->watching);
  for (all_variables (idx)) {
    if (TERMINATED (lucky_terminated_1))
      return false;
    if (!ACTIVE (idx))
      continue;
    const unsigned lit = LIT (idx);
    for (all_binary_blocking_watches (watch, WATCHES (lit))) {
      if (!watch.type.binary)
        continue;
      const unsigned other = watch.binary.lit;
      if (!NEGATED (other) && ACTIVE (IDX (other))) {
        kissat_verbose (solver, "found all positive binary clause");
        return false;
      }
    }
  }
  kissat_message (solver, "lucky no all-positive clause");
  return true;
}

static int forward_false_satisfiable (struct kissat *solver) {
  assert (!solver->level);
#ifndef QUIET
  unsigned conflicts = 0;
#endif
  for (all_stack (import, import, solver->import)) {
    if (TERMINATED (lucky_terminated_1)) {
      kissat_backtrack_without_updating_phases (solver, 0);
      return 0;
    }
    if (!import.imported)
      continue;
    if (import.eliminated)
      continue;
    const unsigned lit = import.lit;
    const unsigned idx = IDX (lit);
    if (!ACTIVE (idx))
      continue;
    if (VALUE (lit))
      continue;
    const unsigned not_lit = NOT (lit);
    kissat_internal_assume (solver, not_lit);
    clause *c = kissat_probing_propagate (solver, 0, true);
    if (!c)
      continue;
#ifndef QUIET
    conflicts++;
#endif
    if (solver->level > 1) {
      kissat_backtrack_without_updating_phases (solver, solver->level - 1);
      kissat_internal_assume (solver, lit);
      clause *d = kissat_probing_propagate (solver, 0, true);
      if (!d)
        continue;
      kissat_verbose (solver,
                      "inconsistency after %u conflicts "
                      "forward assigning %u variables to false",
                      conflicts, solver->level);
      kissat_backtrack_without_updating_phases (solver, 0);
      return 0;
    } else {
      LOG ("failed literal %s", LOGLIT (not_lit));
      kissat_analyze (solver, c);
      assert (!solver->level);
      clause *d = kissat_probing_propagate (solver, 0, true);
      if (d) {
        kissat_analyze (solver, d);
        assert (solver->inconsistent);
        kissat_verbose (solver,
                        "lucky inconsistency forward assigning to false");
        return 20;
      }
    }
  }

  kissat_message (solver, "lucky in forward setting literals to false");
  return 10;
}

static int forward_true_satisfiable (struct kissat *solver) {
  assert (!solver->level);
#ifndef QUIET
  unsigned conflicts = 0;
#endif
  for (all_stack (import, import, solver->import)) {
    if (TERMINATED (lucky_terminated_1)) {
      kissat_backtrack_without_updating_phases (solver, 0);
      return 0;
    }
    if (!import.imported)
      continue;
    if (import.eliminated)
      continue;
    const unsigned lit = import.lit;
    const unsigned idx = IDX (lit);
    if (!ACTIVE (idx))
      continue;
    if (VALUE (lit))
      continue;
    kissat_internal_assume (solver, lit);
    clause *c = kissat_probing_propagate (solver, 0, true);
    if (!c)
      continue;
#ifndef QUIET
    conflicts++;
#endif
    if (solver->level > 1) {
      kissat_backtrack_without_updating_phases (solver, solver->level - 1);
      const unsigned not_lit = NOT (lit);
      kissat_internal_assume (solver, not_lit);
      clause *d = kissat_probing_propagate (solver, 0, true);
      if (!d)
        continue;
      kissat_verbose (solver,
                      "inconsistency after %u conflicts "
                      "forward assigning %u variables to true",
                      conflicts, solver->level);
      kissat_backtrack_without_updating_phases (solver, 0);
      return 0;
    } else {
      LOG ("failed literal %s", LOGLIT (lit));
      kissat_analyze (solver, c);
      assert (!solver->level);
      clause *d = kissat_probing_propagate (solver, 0, true);
      if (d) {
        kissat_analyze (solver, d);
        assert (solver->inconsistent);
        kissat_verbose (solver,
                        "lucky inconsistency forward assigning to true");
        return 20;
      }
    }
  }
  kissat_message (solver, "lucky in forward setting literals to true");
  return 10;
}

static int backward_false_satisfiable (struct kissat *solver) {
  assert (!solver->level);
#ifndef QUIET
  unsigned conflicts = 0;
#endif
  import *begin = BEGIN_STACK (solver->import);
  import *end = END_STACK (solver->import);
  import *p = end;
  while (p != begin) {
    if (TERMINATED (lucky_terminated_1)) {
      kissat_backtrack_without_updating_phases (solver, 0);
      return 0;
    }
    const import import = *--p;
    if (!import.imported)
      continue;
    if (import.eliminated)
      continue;
    const unsigned lit = import.lit;
    const unsigned idx = IDX (lit);
    if (!ACTIVE (idx))
      continue;
    if (VALUE (lit))
      continue;
    const unsigned not_lit = NOT (lit);
    kissat_internal_assume (solver, not_lit);
    clause *c = kissat_probing_propagate (solver, 0, true);
    if (!c)
      continue;
#ifndef QUIET
    conflicts++;
#endif
    if (solver->level > 1) {
      kissat_backtrack_without_updating_phases (solver, solver->level - 1);
      kissat_internal_assume (solver, lit);
      clause *d = kissat_probing_propagate (solver, 0, true);
      if (!d)
        continue;
      kissat_verbose (solver,
                      "inconsistency after %u conflicts "
                      "backward assigning %u variables to false",
                      conflicts, solver->level);
      kissat_backtrack_without_updating_phases (solver, 0);
      return 0;
    } else {
      LOG ("failed literal %s", LOGLIT (not_lit));
      kissat_analyze (solver, c);
      assert (!solver->level);
      clause *d = kissat_probing_propagate (solver, 0, true);
      if (d) {
        kissat_analyze (solver, d);
        assert (solver->inconsistent);
        kissat_verbose (solver,
                        "lucky inconsistency backward assigning to false");
        return 20;
      }
    }
  }
  kissat_message (solver, "lucky in backward setting literals to false");
  return 10;
}

static int backward_true_satisfiable (struct kissat *solver) {
  assert (!solver->level);
#ifndef QUIET
  unsigned conflicts = 0;
#endif
  import *begin = BEGIN_STACK (solver->import);
  import *end = END_STACK (solver->import);
  import *p = end;
  while (p != begin) {
    if (TERMINATED (lucky_terminated_1)) {
      kissat_backtrack_without_updating_phases (solver, 0);
      return 0;
    }
    const import import = *--p;
    if (!import.imported)
      continue;
    if (import.eliminated)
      continue;
    const unsigned lit = import.lit;
    const unsigned idx = IDX (lit);
    if (!ACTIVE (idx))
      continue;
    if (VALUE (lit))
      continue;
    kissat_internal_assume (solver, lit);
    clause *c = kissat_probing_propagate (solver, 0, true);
    if (!c)
      continue;
#ifndef QUIET
    conflicts++;
#endif
    if (solver->level > 1) {
      kissat_backtrack_without_updating_phases (solver, solver->level - 1);
      const unsigned not_lit = NOT (lit);
      kissat_internal_assume (solver, not_lit);
      clause *d = kissat_probing_propagate (solver, 0, true);
      if (!d)
        continue;
      kissat_verbose (solver,
                      "inconsistency after %u conflicts "
                      "backward assigning %u variables to true",
                      conflicts, solver->level);
      kissat_backtrack_without_updating_phases (solver, 0);
      return 0;
    } else {
      LOG ("failed literal %s", LOGLIT (lit));
      kissat_analyze (solver, c);
      assert (!solver->level);
      clause *d = kissat_probing_propagate (solver, 0, true);
      if (d) {
        kissat_analyze (solver, d);
        assert (solver->inconsistent);
        kissat_verbose (solver,
                        "lucky inconsistency backward assigning to true");
        return 20;
      }
    }
  }
  kissat_message (solver, "lucky in backward setting literals to true");
  return 10;
}

int kissat_lucky (struct kissat *solver) {

  if (solver->inconsistent)
    return 0;

  if (!GET_OPTION (lucky))
    return 0;

  START (lucky);
  assert (!solver->level);
  assert (!solver->probing);
  solver->probing = true;
  assert (kissat_propagated (solver));

  int res = 0;
  const unsigned active_before = solver->active;

  if (no_all_negative_clauses (solver)) {
    for (all_variables (idx)) {
      if (!res && TERMINATED (lucky_terminated_1))
        goto DONE;
      if (!ACTIVE (idx))
        continue;
      const unsigned lit = LIT (idx);
      if (VALUE (lit))
        continue;
      kissat_internal_assume (solver, lit);
#ifndef NDEBUG
      clause *c =
#endif
          kissat_probing_propagate (solver, 0, true);
      assert (!c);
    }
    kissat_verbose (solver, "set all variables to true");
    assert (kissat_propagated (solver));
    assert (!solver->unassigned);
    res = 10;
  }

  if (!res && TERMINATED (lucky_terminated_1))
    goto DONE;

  if (!res && no_all_positive_clauses (solver)) {
    for (all_variables (idx)) {
      if (!res && TERMINATED (lucky_terminated_1))
        goto DONE;
      if (!ACTIVE (idx))
        continue;
      const unsigned lit = LIT (idx);
      if (VALUE (lit))
        continue;
      const unsigned not_lit = NOT (lit);
      kissat_internal_assume (solver, not_lit);
#ifndef NDEBUG
      clause *c =
#endif
          kissat_probing_propagate (solver, 0, true);
      assert (!c);
    }
    kissat_verbose (solver, "set all variables to false");
    assert (kissat_propagated (solver));
    assert (!solver->unassigned);
    res = 10;
  }

  if (!res && TERMINATED (lucky_terminated_1))
    goto DONE;

  if (!res)
    res = forward_false_satisfiable (solver);

  if (!res && TERMINATED (lucky_terminated_1))
    goto DONE;

  if (!res)
    res = forward_true_satisfiable (solver);

  if (!res && TERMINATED (lucky_terminated_1))
    goto DONE;

  if (!res)
    res = backward_false_satisfiable (solver);

  if (!res && TERMINATED (lucky_terminated_1))
    goto DONE;

  if (!res)
    res = backward_true_satisfiable (solver);

DONE:
  if (!res && solver->level)
    kissat_backtrack_without_updating_phases (solver, 0);

  const unsigned active_after = solver->active;
  const unsigned units = active_before - active_after;

  if (!res && units)
    kissat_message (solver, "lucky %u units", units);

#ifndef QUIET
  bool success = res || units;
#endif
  assert (solver->probing);
  solver->probing = false;
  REPORT (!success, 'l');
  STOP (lucky);

  return res;
}
