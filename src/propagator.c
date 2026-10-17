#include "propagator.h"
#include "analyze.h"
#include "backtrack.h"
#include "decide.h"
#include "error.h"
#include "inline.h"
#include "inlineframes.h"
#include "require.h"

#include <limits.h>
#include <string.h>

/*------------------------------------------------------------------------*/

// External propagation through the IPASIR-UP interface, an STP extension
// that lets a theory take part in the CDCL search.
//
// Notifications follow the trail. The propagator hears, in trail order,
// every assignment of an observed variable made by the search, with a new
// decision level announced where the trail crosses into one. Nothing it
// hears comes from probing, warming up or local search, which happen at the
// root and backtrack to it; root assignments those make are told before
// the root trail is flushed, and a variable fixed before it was observed is
// told as a root assignment of its own. A backtrack below a level the
// propagator heard about is told before the trail changes; an assignment
// that chronological backtracking keeps above the new level is told again
// afterwards, at the level it now sits at.
//
// A literal the propagator implies comes with its reason clause at once,
// and that clause goes through the same path as an external clause: it is
// added (redundant for reasons, as the propagator says for the others) and
// then propagates, conflicts or simply waits, whatever the trail makes it.
// A conflicting clause is analyzed like a learned conflict, which also
// handles conflicts below the current level and clauses with a single
// literal on the conflict level. Every clause the propagator hands over
// must only name variables that are active (or fixed) here; observed
// variables are protected from elimination and substitution, so it always
// may name those.
//
// A complete assignment is a model only when the propagator accepts it;
// otherwise the clause it then supplies is added and the search goes on.
// The lucky and greedy shortcuts, which can declare a model without the
// propagator, are skipped while it is connected, and proofs are not traced.

#define PROPAGATOR (&solver->propagator)

void kissat_connect_external_propagator (
    kissat *solver, const kissat_external_propagator *callbacks) {
  kissat_require_initialized (solver);
  kissat_require (callbacks, "zero propagator");
  propagator *p = PROPAGATOR;
  kissat_require (!p->connected, "a propagator is already connected");
  kissat_require (callbacks->notify_assignment &&
                      callbacks->notify_new_decision_level &&
                      callbacks->notify_backtrack &&
                      callbacks->check_found_model &&
                      callbacks->has_external_clause &&
                      callbacks->add_external_clause_lit,
                  "incomplete propagator");
  kissat_require (!callbacks->propagate || callbacks->add_reason_clause_lit,
                  "a propagating propagator needs reasons");
  kissat_require (GET_OPTION (incremental), "enable incremental first");
#ifndef NPROOFS
  kissat_require (!solver->proof,
                  "can not trace a proof with an external propagator");
#endif
  if (solver->level)
    kissat_backtrack_in_consistent_state (solver, 0);
  p->callbacks = *callbacks;
  p->connected = true;
  p->notified = 0;
  p->notified_level = 0;
  p->propagated = INVALID_PROPAGATED;
}

void kissat_disconnect_external_propagator (kissat *solver) {
  kissat_require_initialized (solver);
  propagator *p = PROPAGATOR;
  kissat_require (p->connected, "no propagator connected");
  kissat_reset_observed_vars (solver);
  memset (&p->callbacks, 0, sizeof p->callbacks);
  p->connected = false;
}

static bool observing (propagator *p, unsigned eidx) {
  return eidx < SIZE_STACK (p->observing) &&
         PEEK_STACK (p->observing, eidx);
}

void kissat_add_observed_var (kissat *solver, int evar) {
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (evar);
  propagator *p = PROPAGATOR;
  kissat_require (p->connected, "connect a propagator first");
  const unsigned eidx = ABS (evar);
  if (observing (p, eidx))
    return;
  // At the root, so that a fixed variable can be told as a root assignment.
  if (solver->level)
    kissat_backtrack_in_consistent_state (solver, 0);
  kissat_protect (solver, (int) eidx);
  while (SIZE_STACK (p->observing) <= eidx)
    PUSH_STACK (p->observing, 0);
  POKE_STACK (p->observing, eidx, 1);
  PUSH_STACK (p->observed, (int) eidx);
  const import *const import = &PEEK_STACK (solver->import, eidx);
  assert (import->imported);
  assert (!import->eliminated);
  const unsigned ilit = import->lit;
  const value fixed = kissat_fixed (solver, ilit);
  if (fixed)
    PUSH_STACK (p->fixed, fixed > 0 ? (int) eidx : -(int) eidx);
  else
    FLAGS (IDX (ilit))->observed = true;
}

static void unobserve (kissat *solver, unsigned eidx) {
  propagator *p = PROPAGATOR;
  POKE_STACK (p->observing, eidx, 0);
  const import *const import = &PEEK_STACK (solver->import, eidx);
  if (import->imported && !import->eliminated)
    FLAGS (IDX (import->lit))->observed = false;
  kissat_unprotect (solver, (int) eidx);
}

void kissat_remove_observed_var (kissat *solver, int evar) {
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (evar);
  propagator *p = PROPAGATOR;
  const unsigned eidx = ABS (evar);
  if (!observing (p, eidx))
    return;
  unobserve (solver, eidx);
  int *q = BEGIN_STACK (p->observed);
  for (all_stack (int, other, p->observed))
    if (other != (int) eidx)
      *q++ = other;
  SET_END_OF_STACK (p->observed, q);
  q = BEGIN_STACK (p->fixed);
  for (all_stack (int, lit, p->fixed))
    if (ABS (lit) != (int) eidx)
      *q++ = lit;
  SET_END_OF_STACK (p->fixed, q);
}

void kissat_reset_observed_vars (kissat *solver) {
  kissat_require_initialized (solver);
  propagator *p = PROPAGATOR;
  for (all_stack (int, eidx, p->observed))
    unobserve (solver, (unsigned) eidx);
  CLEAR_STACK (p->observed);
  CLEAR_STACK (p->fixed);
}

void kissat_release_propagator (kissat *solver) {
  propagator *p = PROPAGATOR;
  RELEASE_STACK (p->observed);
  RELEASE_STACK (p->observing);
  RELEASE_STACK (p->fixed);
  RELEASE_STACK (p->notifications);
  RELEASE_STACK (p->literals);
}

/*------------------------------------------------------------------------*/

static void notify_batch (kissat *solver) {
  propagator *p = PROPAGATOR;
  if (EMPTY_STACK (p->notifications))
    return;
  p->callbacks.notify_assignment (p->callbacks.state,
                                  BEGIN_STACK (p->notifications),
                                  SIZE_STACK (p->notifications));
  p->statistics.notified += SIZE_STACK (p->notifications);
  CLEAR_STACK (p->notifications);
}

static void notify_trail (kissat *solver) {
  propagator *p = PROPAGATOR;
  assert (p->connected);
  assert (EMPTY_STACK (p->notifications));
  if (!EMPTY_STACK (p->fixed)) {
    // Observed after being fixed: told at the root (the propagator is at
    // the root whenever such a variable is observed).
    assert (!p->notified_level);
    for (all_stack (int, lit, p->fixed))
      PUSH_STACK (p->notifications, lit);
    CLEAR_STACK (p->fixed);
  }
  const unsigned *const trail = BEGIN_ARRAY (solver->trail);
  const unsigned size = SIZE_ARRAY (solver->trail);
  const flags *const flags = solver->flags;
  for (unsigned pos = p->notified; pos < size; pos++) {
    while (p->notified_level < solver->level &&
           FRAME (p->notified_level + 1).trail <= pos) {
      notify_batch (solver);
      p->callbacks.notify_new_decision_level (p->callbacks.state);
      p->notified_level++;
    }
    const unsigned lit = trail[pos];
    if (!flags[IDX (lit)].observed)
      continue;
    const int elit = kissat_export_literal (solver, lit);
    if (elit && observing (p, ABS (elit)))
      PUSH_STACK (p->notifications, elit);
  }
  notify_batch (solver);
  while (p->notified_level < solver->level) {
    p->callbacks.notify_new_decision_level (p->callbacks.state);
    p->notified_level++;
  }
  p->notified = size;
}

void kissat_propagator_notify (kissat *solver) {
  if (PROPAGATOR->connected && !solver->probing && !solver->warming)
    notify_trail (solver);
}

void kissat_propagator_flush (kissat *solver) {
  propagator *p = PROPAGATOR;
  if (!p->connected)
    return;
  assert (!solver->level);
  // Root assignments, whoever made them, before they leave the trail.
  notify_trail (solver);
  p->notified = 0;
  p->propagated = INVALID_PROPAGATED;
}

void kissat_propagator_backtrack (kissat *solver, unsigned new_level,
                                  unsigned new_end) {
  propagator *p = PROPAGATOR;
  if (!p->connected)
    return;
  if (new_level < p->notified_level) {
    p->callbacks.notify_backtrack (p->callbacks.state, new_level);
    p->notified_level = new_level;
    // What stays assigned above 'new_end' is told again.
    if (p->notified > new_end)
      p->notified = new_end;
  }
  assert (p->notified <= new_end || p->notified_level <= new_level);
  p->propagated = INVALID_PROPAGATED;
}

/*------------------------------------------------------------------------*/

// The internal literal of an external one whose variable is active or
// fixed here, or INVALID_LIT.

static unsigned import_active (kissat *solver, int elit) {
  if (!elit || elit == INT_MIN)
    return INVALID_LIT;
  const unsigned eidx = ABS (elit);
  if (eidx >= SIZE_STACK (solver->import))
    return INVALID_LIT;
  const import *const import = &PEEK_STACK (solver->import, eidx);
  if (!import->imported || import->eliminated || import->extension)
    return INVALID_LIT;
  unsigned ilit = import->lit;
  if (elit < 0)
    ilit = NOT (ilit);
  const unsigned idx = IDX (ilit);
  if (!ACTIVE (idx) && !FLAGS (idx)->fixed)
    return INVALID_LIT;
  return ilit;
}

static int empty_clause (kissat *solver) {
  if (solver->level)
    kissat_backtrack_in_consistent_state (solver, 0);
  solver->inconsistent = true;
  LOG ("external empty clause");
  CHECK_AND_ADD_EMPTY ();
  ADD_EMPTY_TO_PROOF ();
  return 20;
}

static reference new_clause (kissat *solver, bool redundant) {
  const unsigned size = SIZE_STACK (solver->clause);
  assert (size > 1);
  if (size == 2) {
    const unsigned *const lits = BEGIN_STACK (solver->clause);
    kissat_new_binary_clause (solver, lits[0], lits[1]);
    return INVALID_REF;
  }
  if (redundant) {
    const reference ref = kissat_new_redundant_clause (solver, size);
    kissat_dereference_clause (solver, ref)->used = 1;
    return ref;
  }
  return kissat_new_irredundant_clause (solver);
}

// The clause watched on 'lits[0]' and 'lits[1]' becomes the reason of
// 'lits[0]', the only literal not false.

static void assign_with_reason (kissat *solver, reference ref) {
  const unsigned *const lits = BEGIN_STACK (solver->clause);
  if (ref == INVALID_REF)
    kissat_assign_binary (solver, lits[0], lits[1]);
  else {
    clause *c = kissat_dereference_clause (solver, ref);
    kissat_assign_reference (solver, c->lits[0], ref, c);
  }
}

static void swap_literals (unsigned *lits, unsigned i, unsigned j) {
  const unsigned tmp = lits[i];
  lits[i] = lits[j];
  lits[j] = tmp;
}

// Add the clause in 'propagator.literals', external literals the
// propagator handed over. Returns 0 when the trail did not change, -1 when
// it did (a propagation, a backtrack or an analyzed conflict), 20 when the
// formula became inconsistent, and -2 for a clause naming a variable that
// is not active here, which is dropped.

static int add_external_clause (kissat *solver, bool redundant) {
  propagator *p = PROPAGATOR;
  assert (EMPTY_STACK (solver->clause));
  value *const marks = solver->marks;
  int res = 0;
  for (all_stack (int, elit, p->literals)) {
    const unsigned ilit = import_active (solver, elit);
    if (ilit == INVALID_LIT) {
      res = -2;
      break;
    }
    const value fixed = kissat_fixed (solver, ilit);
    if (fixed > 0) {
      res = 1;
      break;
    }
    if (fixed < 0 || marks[ilit])
      continue;
    if (marks[NOT (ilit)]) {
      res = 1;
      break;
    }
    marks[ilit] = 1;
    PUSH_STACK (solver->clause, ilit);
  }
  for (all_stack (unsigned, ilit, solver->clause))
    marks[ilit] = 0;
  if (res) {
    CLEAR_STACK (solver->clause);
    return res < 0 ? res : 0; // dropped, or satisfied at the root
  }
  ADD_UNCHECKED_EXTERNAL (SIZE_STACK (p->literals),
                          BEGIN_STACK (p->literals));
  p->statistics.clauses++;
  const unsigned size = SIZE_STACK (solver->clause);
  if (!size)
    return empty_clause (solver);
  unsigned *lits = BEGIN_STACK (solver->clause);
  if (size == 1) {
    const unsigned unit = lits[0];
    CLEAR_STACK (solver->clause);
    if (VALUE (unit))
      kissat_backtrack_in_consistent_state (solver, 0);
    assert (!VALUE (unit));
    kissat_learned_unit (solver, unit);
    return -1;
  }
  // Open literals first; then, of the assigned ones, the true literal on
  // the lowest level and the literal on the highest level.
  unsigned open = 0;
  for (unsigned i = 0; i < size; i++)
    if (!VALUE (lits[i]))
      swap_literals (lits, open++, i);
  if (open > 1) {
    (void) new_clause (solver, redundant);
    CLEAR_STACK (solver->clause);
    return 0;
  }
  unsigned lowest_true = INVALID_LEVEL, highest = INVALID_LEVEL;
  unsigned lowest_true_pos = size, highest_pos = size;
  for (unsigned i = open; i < size; i++) {
    const unsigned lit = lits[i];
    const unsigned level = LEVEL (lit);
    if (VALUE (lit) > 0 &&
        (lowest_true == INVALID_LEVEL || level < lowest_true))
      lowest_true = level, lowest_true_pos = i;
  }
  if (open == 1) {
    if (lowest_true != INVALID_LEVEL) {
      // Satisfied, and watched on the open literal and a true one.
      swap_literals (lits, 1, lowest_true_pos);
      (void) new_clause (solver, redundant);
      CLEAR_STACK (solver->clause);
      return 0;
    }
    // Propagating: every other literal is false.
    for (unsigned i = 1; i < size; i++) {
      const unsigned level = LEVEL (lits[i]);
      if (highest == INVALID_LEVEL || level > highest)
        highest = level, highest_pos = i;
    }
    swap_literals (lits, 1, highest_pos);
    const reference ref = new_clause (solver, redundant);
    assign_with_reason (solver, ref);
    CLEAR_STACK (solver->clause);
    p->statistics.propagated++;
    return -1;
  }
  assert (!open);
  if (lowest_true != INVALID_LEVEL) {
    swap_literals (lits, 0, lowest_true_pos);
    for (unsigned i = 1; i < size; i++) {
      const unsigned level = LEVEL (lits[i]);
      if (highest == INVALID_LEVEL || level > highest)
        highest = level, highest_pos = i;
    }
    swap_literals (lits, 1, highest_pos);
    if (lowest_true <= highest) {
      // Satisfied no later than the highest other literal was assigned.
      (void) new_clause (solver, redundant);
      CLEAR_STACK (solver->clause);
      return 0;
    }
    // Every other literal is false below the true one: the clause implies
    // it there. Backtrack under it and propagate it on the right level.
    kissat_backtrack_in_consistent_state (solver, highest);
    assert (!VALUE (lits[0]));
    const reference ref = new_clause (solver, redundant);
    assign_with_reason (solver, ref);
    CLEAR_STACK (solver->clause);
    p->statistics.propagated++;
    return -1;
  }
  // Every literal is false: a conflict, analyzed as a learned one.
  for (unsigned i = 0; i < 2; i++) {
    highest = INVALID_LEVEL;
    for (unsigned j = i; j < size; j++) {
      const unsigned level = LEVEL (lits[j]);
      if (highest == INVALID_LEVEL || level > highest)
        highest = level, highest_pos = j;
    }
    swap_literals (lits, i, highest_pos);
  }
  const reference ref = new_clause (solver, redundant);
  clause *conflict;
  if (ref == INVALID_REF)
    conflict = kissat_binary_conflict (solver, lits[0], lits[1]);
  else
    conflict = kissat_dereference_clause (solver, ref);
  CLEAR_STACK (solver->clause);
  p->statistics.conflicts++;
  return kissat_analyze (solver, conflict) == 20 ? 20 : -1;
}

static void read_external_clause (kissat *solver) {
  propagator *p = PROPAGATOR;
  CLEAR_STACK (p->literals);
  for (int elit;
       (elit = p->callbacks.add_external_clause_lit (p->callbacks.state));)
    PUSH_STACK (p->literals, elit);
}

static int propagate_literal (kissat *solver, int elit) {
  propagator *p = PROPAGATOR;
  const unsigned ilit = import_active (solver, elit);
  if (ilit == INVALID_LIT || VALUE (ilit) > 0)
    return 0;
  CLEAR_STACK (p->literals);
  bool contained = false;
  for (int other; (other = p->callbacks.add_reason_clause_lit (
                       p->callbacks.state, elit));) {
    contained = contained || other == elit;
    PUSH_STACK (p->literals, other);
  }
  if (!contained)
    return 0;
  const int res = add_external_clause (solver, true);
  return res == -2 ? 0 : res;
}

int kissat_propagator_propagate (kissat *solver) {
  propagator *p = PROPAGATOR;
  assert (p->connected);
  assert (!solver->inconsistent);
  assert (!solver->probing);
  void *const state = p->callbacks.state;
  if (p->callbacks.propagate)
    for (;;) {
      notify_trail (solver);
      const int elit = p->callbacks.propagate (state);
      if (!elit)
        break;
      const int res = propagate_literal (solver, elit);
      if (res)
        return res;
    }
  for (;;) {
    notify_trail (solver);
    int forgettable = 0;
    if (!p->callbacks.has_external_clause (state, &forgettable))
      break;
    read_external_clause (solver);
    const int res = add_external_clause (solver, forgettable);
    if (res == 20 || res == -1)
      return res;
  }
  p->propagated = SIZE_ARRAY (solver->trail);
  return 0;
}

int kissat_propagator_check_model (kissat *solver) {
  propagator *p = PROPAGATOR;
  assert (p->connected);
  assert (!solver->unassigned);
  notify_trail (solver);
  CLEAR_STACK (p->literals);
  for (all_stack (int, eidx, p->observed)) {
    const import *const import = &PEEK_STACK (solver->import, eidx);
    assert (import->imported);
    assert (!import->eliminated);
    const value value = VALUE (import->lit);
    assert (value);
    PUSH_STACK (p->literals, value > 0 ? eidx : -eidx);
  }
  p->statistics.checks++;
  void *const state = p->callbacks.state;
  if (p->callbacks.check_found_model (state, BEGIN_STACK (p->literals),
                                      SIZE_STACK (p->literals)))
    return 10;
  p->statistics.rejected++;
  int forgettable = 0;
  while (p->callbacks.has_external_clause (state, &forgettable)) {
    read_external_clause (solver);
    const int res = add_external_clause (solver, forgettable);
    if (res == 20)
      return 20;
    if (res == -1)
      return 0;
  }
  // Rejected without a clause that the assignment falsifies: give up.
  return -1;
}

bool kissat_propagator_decide (kissat *solver) {
  propagator *p = PROPAGATOR;
  if (!p->connected || !p->callbacks.decide)
    return false;
  notify_trail (solver);
  const int elit = p->callbacks.decide (p->callbacks.state);
  if (!elit)
    return false;
  const unsigned ilit = import_active (solver, elit);
  if (ilit == INVALID_LIT || VALUE (ilit))
    return false;
  p->statistics.decisions++;
  INC (decisions);
  kissat_internal_assume (solver, ilit);
  return true;
}

int kissat_propagator_advise (kissat *solver, unsigned idx, int value) {
  propagator *p = PROPAGATOR;
  assert (p->connected);
  assert (p->callbacks.advise_decision_polarity);
  const int elit = kissat_export_literal (solver, LIT (idx));
  if (!elit || !observing (p, ABS (elit)))
    return value;
  notify_trail (solver);
  const int offered = value > 0 ? elit : -elit;
  const int advised =
      p->callbacks.advise_decision_polarity (p->callbacks.state, offered);
  if (advised != -offered)
    return value;
  p->statistics.advised++;
  return -value;
}

int kissat_is_decision (kissat *solver, int elit) {
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (elit);
  const unsigned ilit = import_active (solver, elit);
  if (ilit == INVALID_LIT || !VALUE (ilit))
    return 0;
  const assigned *const a = ASSIGNED (ilit);
  return a->level && !a->binary && a->reason == DECISION_REASON;
}
