#include "exchange.h"
#include "backtrack.h"
#include "error.h"
#include "inline.h"
#include "inlineheap.h"
#include "inlinequeue.h"
#include "require.h"

#include <limits.h>

/*------------------------------------------------------------------------*/

// Learned-clause exchange and search diversification, an STP extension for
// solvers forked from one loaded solver which exchange learned clauses.
//
// Export. Every clause of at most 'max_size' literals that conflict
// analysis learns, and every unit that any technique derives at the root,
// is handed over in external literals. A clause naming a variable that has
// no external counterpart or that the solver introduced itself ('factor')
// is kept back: its meaning is private to this copy.
//
// Import. Every imported clause is promised to be implied by the clauses
// added to this solver. Such a clause can be added as a redundant clause
// whatever inprocessing has done, provided every one of its variables is
// still active here: the enabled techniques only add implied clauses,
// remove clauses, eliminate or substitute variables (keeping what is
// needed to extend a model) or introduce fresh variables ('factor'), so
// every model of the added clauses, extended to the fresh variables, stays
// a model of what remains, and an implied clause excludes none of them.
// A clause over an eliminated, substituted, fresh or unused variable is
// dropped instead of restoring that variable.
//
// Clauses are imported between propagation and the next decision, so the
// watch invariants hold. A clause with at least two unassigned literals is
// watched on two of them at once; any other clause, and every unit, makes
// the solver backtrack first: units to the root, other clauses to the
// highest level at which two of their literals are unassigned. One poll
// backtracks at most once, to the lowest level any of its clauses needs.
// Nothing is imported while a proof is written. The checker of debugging
// builds takes every imported clause as an original one.

void kissat_set_learn (kissat *solver, void *state, unsigned max_size,
                       void (*learn) (void *state, unsigned size,
                                      const int *clause)) {
  kissat_require_initialized (solver);
  kissat_require_outside_callbacks (solver);
  exchange *exchange = &solver->exchange;
  exchange->learn_state = state;
  exchange->learn = learn;
  exchange->max_size = learn ? max_size : 0;
}

void kissat_set_import (kissat *solver, void *state, unsigned interval,
                        unsigned (*budget) (void *state),
                        const int *(*next) (void *state, unsigned *size)) {
  kissat_require_initialized (solver);
  kissat_require_outside_callbacks (solver);
  exchange *exchange = &solver->exchange;
  exchange->import_state = state;
  exchange->budget = budget;
  exchange->next = next;
  exchange->interval = interval;
  exchange->limit = CONFLICTS;
}

void kissat_get_import_statistics (kissat *solver,
                                   kissat_import_statistics *statistics) {
  kissat_require_initialized (solver);
  kissat_require (statistics, "zero statistics pointer");
  *statistics = solver->exchange.statistics;
}

void kissat_release_exchange (kissat *solver) {
  RELEASE_STACK (solver->exchange.exported);
  RELEASE_STACK (solver->exchange.accepted);
}

/*------------------------------------------------------------------------*/

void kissat_export_clause (kissat *solver, unsigned size,
                           const unsigned *lits) {
  exchange *exchange = &solver->exchange;
  assert (exchange->learn);
  assert (size <= exchange->max_size);
  CLEAR_STACK (exchange->exported);
  const import *const imports = BEGIN_STACK (solver->import);
  for (unsigned i = 0; i < size; i++) {
    const int elit = kissat_export_literal (solver, lits[i]);
    if (!elit)
      return;
    if (imports[ABS (elit)].extension)
      return;
    PUSH_STACK (exchange->exported, elit);
  }
  exchange->learn (exchange->learn_state, size,
                   BEGIN_STACK (exchange->exported));
}

/*------------------------------------------------------------------------*/

static int import_empty_clause (kissat *solver) {
  if (solver->level)
    kissat_backtrack_in_consistent_state (solver, 0);
  solver->inconsistent = true;
  LOG ("imported empty clause");
  CHECK_AND_ADD_EMPTY ();
  ADD_EMPTY_TO_PROOF ();
  return 20;
}

// Map one imported clause into 'solver->clause' in internal literals,
// without the literals falsified at the root. Returns -1 when it is
// dropped, 1 when it is satisfied (or a tautology) and 0 otherwise.

static int map_imported_clause (kissat *solver, unsigned size,
                                const int *elits) {
  assert (EMPTY_STACK (solver->clause));
  const size_t imported = SIZE_STACK (solver->import);
  value *const marks = solver->marks;
  int res = size ? 0 : -1;
  for (unsigned i = 0; !res && i < size; i++) {
    const int elit = elits[i];
    if (!elit || elit == INT_MIN) {
      res = -1;
      break;
    }
    const unsigned eidx = ABS (elit);
    if (eidx >= imported) {
      res = -1;
      break;
    }
    const import *const import = &PEEK_STACK (solver->import, eidx);
    if (!import->imported || import->eliminated || import->extension) {
      res = -1;
      break;
    }
    unsigned ilit = import->lit;
    if (elit < 0)
      ilit = NOT (ilit);
    const value fixed = kissat_fixed (solver, ilit);
    if (fixed > 0) {
      res = 1;
      break;
    }
    if (fixed < 0)
      continue;
    if (!ACTIVE (IDX (ilit))) {
      res = -1;
      break;
    }
    if (marks[ilit])
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
  if (res)
    CLEAR_STACK (solver->clause);
  else
    ADD_UNCHECKED_EXTERNAL (size, elits);
  return res;
}

// The level at which the clause in 'solver->clause' can be watched: the
// root for a unit; otherwise the highest level leaving two of its
// literals unassigned.

static unsigned needed_level (kissat *solver) {
  const unsigned size = SIZE_STACK (solver->clause);
  assert (size);
  if (size == 1)
    return 0;
  unsigned open = 0, first = 0, second = 0;
  for (all_stack (unsigned, ilit, solver->clause)) {
    if (!VALUE (ilit)) {
      open++;
      continue;
    }
    const unsigned level = LEVEL (ilit);
    assert (level);
    if (level > first)
      second = first, first = level;
    else if (level > second)
      second = level;
  }
  if (open > 1)
    return solver->level;
  if (open == 1)
    return first - 1;
  assert (second);
  return second - 1;
}

int kissat_import_clauses (kissat *solver) {
  exchange *exchange = &solver->exchange;
  assert (exchange->next);
  assert (!solver->probing);
  assert (solver->watching);
  exchange->limit =
      CONFLICTS + (exchange->interval ? exchange->interval : 1);
  kissat_import_statistics *statistics = &exchange->statistics;
  statistics->polls++;
  if (solver->inconsistent)
    return 20;
#ifndef NPROOFS
  if (solver->proof)
    return 0;
#endif
  unsigneds *accepted = &exchange->accepted;
  CLEAR_STACK (*accepted);
  unsigned target = solver->level;
  const unsigned budget = exchange->budget
                              ? exchange->budget (exchange->import_state)
                              : UINT_MAX;
  uint64_t longer = 0;
  for (;;) {
    unsigned size = 0;
    const int *elits = exchange->next (exchange->import_state, &size);
    if (!elits)
      break;
    if (size > 1 && longer++ >= budget) {
      statistics->dropped++; // beyond the budget: the importer's fault
      break;
    }
    const int mapped = map_imported_clause (solver, size, elits);
    if (mapped < 0) {
      statistics->dropped++;
      continue;
    }
    if (mapped > 0) {
      statistics->satisfied++;
      continue;
    }
    if (EMPTY_STACK (solver->clause)) {
      // Every literal is false at the root: the formula is unsatisfiable.
      statistics->clauses++;
      return import_empty_clause (solver);
    }
    const unsigned needed = needed_level (solver);
    if (needed < target)
      target = needed;
    for (all_stack (unsigned, ilit, solver->clause))
      PUSH_STACK (*accepted, ilit);
    PUSH_STACK (*accepted, INVALID_LIT);
    CLEAR_STACK (solver->clause);
  }
  if (EMPTY_STACK (*accepted))
    return 0;
  if (target < solver->level) {
    statistics->backtracks++;
    kissat_backtrack_in_consistent_state (solver, target);
  }

  // Add what was accepted. Units first, at the root; a unit falsified by an
  // earlier unit of this poll refutes the formula. The accepted stack is
  // not touched while it is traversed, so iterating over it is safe.
  const unsigned *const end = END_STACK (*accepted);
  for (const unsigned *p = BEGIN_STACK (*accepted), *q; p != end;
       p = q + 1) {
    q = p;
    while (*q != INVALID_LIT)
      q++;
    if (q - p != 1)
      continue;
    assert (!solver->level);
    const unsigned ilit = *p;
    const value tmp = VALUE (ilit);
    if (tmp > 0)
      continue;
    statistics->clauses++;
    statistics->units++;
    if (tmp < 0)
      return import_empty_clause (solver);
    kissat_assign_unit (solver, ilit, "imported");
  }
  for (const unsigned *p = BEGIN_STACK (*accepted), *q; p != end;
       p = q + 1) {
    q = p;
    while (*q != INVALID_LIT)
      q++;
    if (q - p < 2)
      continue;
    assert (EMPTY_STACK (solver->clause));
    // Two unassigned literals go first and are watched; a literal fixed at
    // the root by a unit of this poll satisfies or shortens the clause.
    bool satisfied = false;
    unsigned open = 0;
    for (const unsigned *l = p; l != q; l++) {
      const unsigned ilit = *l;
      const value fixed = kissat_fixed (solver, ilit);
      if (fixed > 0) {
        satisfied = true;
        break;
      }
      if (fixed < 0)
        continue;
      PUSH_STACK (solver->clause, ilit);
      if (!VALUE (ilit) && open < 2) {
        unsigned *lits = BEGIN_STACK (solver->clause);
        const size_t last = SIZE_STACK (solver->clause) - 1;
        const unsigned tmp = lits[open];
        lits[open] = lits[last];
        lits[last] = tmp;
        open++;
      }
    }
    if (satisfied || open < 2) {
      // Only units of this poll can have made this happen: satisfied by
      // one, or shortened by them below two open literals (dropped, best
      // effort).
      if (satisfied)
        statistics->satisfied++;
      else
        statistics->dropped++;
      CLEAR_STACK (solver->clause);
      continue;
    }
    const unsigned size = SIZE_STACK (solver->clause);
    const reference ref = kissat_new_redundant_clause (solver, size);
    if (ref != INVALID_REF) {
      clause *c = kissat_dereference_clause (solver, ref);
      c->used = 1;
    }
    CLEAR_STACK (solver->clause);
    statistics->clauses++;
  }
  return 0;
}

/*------------------------------------------------------------------------*/

void kissat_diversify (kissat *solver, int seed, int phase, int shuffle) {
  kissat_require_initialized (solver);
  kissat_require_outside_callbacks (solver);
  kissat_require (seed >= 0, "negative seed");
  if (solver->level)
    kissat_backtrack_in_consistent_state (solver, 0);
#ifndef NOPTIONS
  kissat_options_set (&solver->options, "seed", seed);
#endif
  solver->random = (unsigned) seed;
  generator random = (unsigned) seed;
  if (-1 <= phase && phase <= 1) {
    // Only active variables: one activated later starts without a saved
    // phase.
    value *saved = solver->phases.saved;
    for (all_variables (idx))
      if (ACTIVE (idx))
        saved[idx] = phase > 0   ? 1
                     : phase < 0 ? -1
                                 : (kissat_pick_bool (&random) ? 1 : -1);
  }
  if (!shuffle)
    return;
  unsigneds order;
  INIT_STACK (order);
  for (all_variables (idx))
    if (ACTIVE (idx))
      PUSH_STACK (order, idx);
  unsigned *idxs = BEGIN_STACK (order);
  const unsigned size = SIZE_STACK (order);
  for (unsigned i = size; i > 1; i--) {
    const unsigned j = kissat_pick_random (&random, 0, i);
    const unsigned tmp = idxs[i - 1];
    idxs[i - 1] = idxs[j];
    idxs[j] = tmp;
  }
  heap *scores = SCORES;
  for (unsigned i = 0; i < size; i++) {
    const unsigned idx = idxs[i];
    kissat_move_to_front (solver, idx);
    kissat_update_heap (solver, scores, idx, kissat_pick_double (&random));
  }
  RELEASE_STACK (order);
}
