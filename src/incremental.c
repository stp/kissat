#include "incremental.h"
#include "analyze.h"
#include "import.h"
#include "inline.h"
#include "inlineframes.h"

#include <string.h>

static void failed_assumptions (kissat *solver, int elit, unsigned failing) {
  assert (EMPTY_STACK (solver->analyzed));
  PUSH_STACK (solver->failed, elit);
  if (!LEVEL (failing))
    return;
  kissat_push_analyzed (solver, solver->assigned, IDX (failing));
  unsigned unresolved = 1;
  unsigned const *trail = END_ARRAY (solver->trail);
  while (unresolved) {
    unsigned lit;
    assigned *a;
    do {
      assert (trail > BEGIN_ARRAY (solver->trail));
      lit = *--trail;
      a = ASSIGNED (lit);
    } while (!a->analyzed);
    unresolved--;
    if (a->reason == DECISION_REASON) {
      assert (a->level && a->level <=
                             SIZE_STACK (solver->assumption_decisions));
      const int reason =
          PEEK_STACK (solver->assumption_decisions, a->level - 1);
      PUSH_STACK (solver->failed, reason);
    } else if (a->binary) {
      const unsigned other = a->reason;
      if (LEVEL (other) && !ASSIGNED (other)->analyzed) {
        kissat_push_analyzed (solver, solver->assigned, IDX (other));
        unresolved++;
      }
    } else {
      assert (a->reason != UNIT_REASON);
      clause *reason = kissat_dereference_clause (solver, a->reason);
      for (all_literals_in_clause (other, reason)) {
        if (other != lit && LEVEL (other) && !ASSIGNED (other)->analyzed) {
          kissat_push_analyzed (solver, solver->assigned, IDX (other));
          unresolved++;
        }
      }
    }
  }
  kissat_reset_only_analyzed_literals (solver);
}

int kissat_assign_assumption (kissat *solver) {
  assert (kissat_assuming (solver));
  while (kissat_assuming (solver)) {
    const bool replay = solver->level < SIZE_STACK (solver->assumption_decisions);
    const int elit = replay
                         ? PEEK_STACK (solver->assumption_decisions, solver->level)
                         : PEEK_STACK (solver->assumptions, solver->assumption_next);
    if (!replay)
      solver->assumption_next++;
    const unsigned ilit = kissat_import_literal (solver, elit);
    assert (ilit != INVALID_LIT);
    const value v = VALUE (ilit);
    if (v < 0) {
      failed_assumptions (solver, elit, ilit);
      return 20;
    }
    if (v > 0) {
      // An implied assumption needs no decision frame. Kissat's restart
      // and conflict analysis require every non-root frame to be nonempty.
      if (replay) {
        const size_t left = SIZE_STACK (solver->assumption_decisions) -
                            solver->level - 1;
        int *p = BEGIN_STACK (solver->assumption_decisions) + solver->level;
        memmove (p, p + 1, left * sizeof *p);
        (void) POP_STACK (solver->assumption_decisions);
      }
      continue;
    }
    if (!replay)
      PUSH_STACK (solver->assumption_decisions, elit);
    solver->level++;
    kissat_push_frame (solver, ilit);
    kissat_assign_decision (solver, ilit);
    break;
  }
  return 0;
}
