#include "allocate.h"
#include "backtrack.h"
#include "error.h"
#include "import.h"
#include "inline.h"
#include "inlineframes.h"
#include "print.h"
#include "propsearch.h"
#include "require.h"
#include "resize.h"
#include "resources.h"
#include "search.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void kissat_reset_last_learned (kissat *solver) {
  for (really_all_last_learned (p))
    *p = INVALID_REF;
}

kissat *kissat_init (void) {
  kissat *solver = kissat_calloc (0, 1, sizeof *solver);
#ifndef NOPTIONS
  kissat_init_options (&solver->options);
#else
  kissat_init_options ();
#endif
#ifndef QUIET
  kissat_init_profiles (&solver->profiles);
#endif
  START (total);
  kissat_init_queue (solver);
  assert (INTERNAL_MAX_LIT < UINT_MAX);
  kissat_push_frame (solver, UINT_MAX);
  solver->watching = true;
  solver->conflict.size = 2;
  solver->scinc = 1.0;
  solver->first_reducible = INVALID_REF;
  solver->last_irredundant = INVALID_REF;
  kissat_reset_last_learned (solver);
#ifndef NDEBUG
  kissat_init_checker (solver);
#endif
  solver->prefix = kissat_strdup (solver, "c ");
  return solver;
}

void kissat_set_prefix (kissat *solver, const char *prefix) {
  kissat_freestr (solver, solver->prefix);
  solver->prefix = kissat_strdup (solver, prefix);
}

#define DEALLOC_GENERIC(NAME, ELEMENTS_PER_BLOCK) \
  do { \
    const size_t block_size = ELEMENTS_PER_BLOCK * sizeof *solver->NAME; \
    kissat_dealloc (solver, solver->NAME, solver->size, block_size); \
    solver->NAME = 0; \
  } while (0)

#define DEALLOC_VARIABLE_INDEXED(NAME) DEALLOC_GENERIC (NAME, 1)

#define DEALLOC_LITERAL_INDEXED(NAME) DEALLOC_GENERIC (NAME, 2)

#define RELEASE_LITERAL_INDEXED_STACKS(NAME, ACCESS) \
  do { \
    for (all_stack (unsigned, IDX_RILIS, solver->active)) { \
      const unsigned LIT_RILIS = LIT (IDX_RILIS); \
      const unsigned NOT_LIT_RILIS = NOT (LIT_RILIS); \
      RELEASE_STACK (ACCESS (LIT_RILIS)); \
      RELEASE_STACK (ACCESS (NOT_LIT_RILIS)); \
    } \
    DEALLOC_LITERAL_INDEXED (NAME); \
  } while (0)

void kissat_release (kissat *solver) {
  kissat_require_initialized (solver);
  kissat_release_heap (solver, SCORES);
  kissat_release_heap (solver, &solver->schedule);
  kissat_release_vectors (solver);
  kissat_release_phases (solver);

  RELEASE_STACK (solver->pending);
  RELEASE_STACK (solver->assumptions);
  RELEASE_STACK (solver->assumption_decisions);
  RELEASE_STACK (solver->previous_assumptions);
  RELEASE_STACK (solver->failed);
  RELEASE_STACK (solver->export);
  RELEASE_STACK (solver->import);

  DEALLOC_VARIABLE_INDEXED (assigned);
  DEALLOC_VARIABLE_INDEXED (flags);
  DEALLOC_VARIABLE_INDEXED (links);

  DEALLOC_LITERAL_INDEXED (marks);
  DEALLOC_LITERAL_INDEXED (values);
  DEALLOC_LITERAL_INDEXED (watches);

  RELEASE_STACK (solver->import);
  RELEASE_STACK (solver->eliminated);
  RELEASE_STACK (solver->extend);
  RELEASE_STACK (solver->witness);
  RELEASE_STACK (solver->etrail);

  RELEASE_STACK (solver->delayed);

  RELEASE_STACK (solver->clause);
  RELEASE_STACK (solver->shadow);
#if defined(LOGGING) || !defined(NDEBUG)
  RELEASE_STACK (solver->resolvent);
#endif

  RELEASE_STACK (solver->arena);

  RELEASE_STACK (solver->units);
  RELEASE_STACK (solver->frames);
  RELEASE_STACK (solver->sorter);

  RELEASE_ARRAY (solver->trail, solver->size);

  RELEASE_STACK (solver->analyzed);
  RELEASE_STACK (solver->levels);
  RELEASE_STACK (solver->minimize);
  RELEASE_STACK (solver->poisoned);
  RELEASE_STACK (solver->promote);
  RELEASE_STACK (solver->removable);
  RELEASE_STACK (solver->shrinkable);
  RELEASE_STACK (solver->xorted[0]);
  RELEASE_STACK (solver->xorted[1]);

  RELEASE_STACK (solver->sweep_schedule);

  RELEASE_STACK (solver->ranks);

  RELEASE_STACK (solver->antecedents[0]);
  RELEASE_STACK (solver->antecedents[1]);
  RELEASE_STACK (solver->gates[0]);
  RELEASE_STACK (solver->gates[1]);
  RELEASE_STACK (solver->resolvents);

#if !defined(NDEBUG) || !defined(NPROOFS)
  RELEASE_STACK (solver->added);
  RELEASE_STACK (solver->removed);
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  RELEASE_STACK (solver->original);
#endif

#ifndef QUIET
  RELEASE_STACK (solver->profiles.stack);
#endif

  kissat_freestr (solver, solver->prefix);

#ifndef NDEBUG
  kissat_release_checker (solver);
#endif
#if !defined(NDEBUG) && defined(METRICS)
  uint64_t leaked = solver->statistics.allocated_current;
  if (leaked)
    if (!getenv ("LEAK"))
      kissat_fatal ("internally leaking %" PRIu64 " bytes", leaked);
#endif

  kissat_free (0, solver, sizeof *solver);
}

void kissat_reserve (kissat *solver, int max_var) {
  kissat_require_initialized (solver);
  kissat_require (0 <= max_var, "negative maximum variable argument '%d'",
                  max_var);
  kissat_require (max_var <= EXTERNAL_MAX_VAR,
                  "invalid maximum variable argument '%d'", max_var);
  if (GET_OPTION (incremental)) {
    // Reserve the external namespace too. Factoring allocates immediately
    // above the import table, including variables not yet used in clauses.
    if (max_var)
      (void) kissat_import_literal (solver, max_var);
    return;
  }
  kissat_increase_size (solver, (unsigned) max_var);
  if (!GET_OPTION (tumble)) {
    for (int idx = 1; idx <= max_var; idx++)
      (void) kissat_import_literal (solver, idx);
    for (unsigned idx = 0; idx != (unsigned) max_var; idx++)
      kissat_activate_literal (solver, LIT (idx));
  }
}

int kissat_get_option (kissat *solver, const char *name) {
  kissat_require_initialized (solver);
  kissat_require (name, "name zero pointer");
#ifndef NOPTIONS
  return kissat_options_get (&solver->options, name);
#else
  (void) solver;
  return kissat_options_get (name);
#endif
}

int kissat_set_option (kissat *solver, const char *name, int new_value) {
#ifndef NOPTIONS
  kissat_require_initialized (solver);
  kissat_require (name, "name zero pointer");
  if (solver->solve_calls && !strcmp (name, "incremental"))
    kissat_require (new_value == GET_OPTION (incremental),
                    "incremental mode must be selected before first solve");
#ifndef NOPTIONS
  return kissat_options_set (&solver->options, name, new_value);
#else
  return kissat_options_set (name, new_value);
#endif
#else
  (void) solver, (void) new_value;
  return kissat_options_get (name);
#endif
}

void kissat_set_decision_limit (kissat *solver, unsigned limit) {
  kissat_require_initialized (solver);
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  statistics *statistics = &solver->statistics;
  limited->decisions = true;
  assert (UINT64_MAX - limit >= statistics->decisions);
  limits->decisions = statistics->decisions + limit;
  LOG ("set decision limit to %" PRIu64 " after %u decisions",
       limits->decisions, limit);
}

void kissat_set_conflict_limit (kissat *solver, unsigned limit) {
  kissat_require_initialized (solver);
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  statistics *statistics = &solver->statistics;
  limited->conflicts = true;
  assert (UINT64_MAX - limit >= statistics->conflicts);
  limits->conflicts = statistics->conflicts + limit;
  LOG ("set conflict limit to %" PRIu64 " after %u conflicts",
       limits->conflicts, limit);
}

void kissat_print_statistics (kissat *solver) {
#ifndef QUIET
  kissat_require_initialized (solver);
  const int verbosity = kissat_verbosity (solver);
  if (verbosity < 0)
    return;
  if (GET_OPTION (profile)) {
    kissat_section (solver, "profiling");
    kissat_profiles_print (solver);
  }
  const bool complete = GET_OPTION (statistics);
  kissat_section (solver, "statistics");
  const bool verbose = (complete || verbosity > 0);
  kissat_statistics_print (solver, verbose);
#ifndef NPROOFS
  if (solver->proof) {
    kissat_section (solver, "proof");
    kissat_print_proof_statistics (solver, verbose);
  }
#endif
#ifndef NDEBUG
  if (GET_OPTION (check) > 1) {
    kissat_section (solver, "checker");
    kissat_print_checker_statistics (solver, verbose);
  }
#endif
  kissat_section (solver, "glue usage");
  kissat_print_glue_usage (solver);
  kissat_section (solver, "resources");
  kissat_print_resources (solver);
#endif
  (void) solver;
}

static void add_original (kissat *solver, int elit) {
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  const int checking = kissat_checking (solver);
  const bool logging = kissat_logging (solver);
  const bool proving = kissat_proving (solver);
#endif
  if (elit) {
    kissat_require_valid_external_internal (elit);
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    if (checking || logging || proving)
      PUSH_STACK (solver->original, elit);
#endif
    unsigned ilit = kissat_import_literal (solver, elit);

    const mark mark = MARK (ilit);
    if (!mark) {
      const value value = kissat_fixed (solver, ilit);
      if (value > 0) {
        if (!solver->clause_satisfied) {
          LOG ("adding root level satisfied literal %u(%d)@0=1", ilit,
               elit);
          solver->clause_satisfied = true;
        }
      } else if (value < 0) {
        LOG ("adding root level falsified literal %u(%d)@0=-1", ilit, elit);
        if (!solver->clause_shrink) {
          solver->clause_shrink = true;
          LOG ("thus original clause needs shrinking");
        }
      } else {
        MARK (ilit) = 1;
        MARK (NOT (ilit)) = -1;
        assert (SIZE_STACK (solver->clause) < UINT_MAX);
        PUSH_STACK (solver->clause, ilit);
      }
    } else if (mark < 0) {
      assert (mark < 0);
      if (!solver->clause_trivial) {
        LOG ("adding dual literal %u(%d) and %u(%d)", NOT (ilit), -elit,
             ilit, elit);
        solver->clause_trivial = true;
      }
    } else {
      assert (mark > 0);
      LOG ("adding duplicated literal %u(%d)", ilit, elit);
      if (!solver->clause_shrink) {
        solver->clause_shrink = true;
        LOG ("thus original clause needs shrinking");
      }
    }
  } else {
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    const size_t offset = solver->offset_of_last_original_clause;
    size_t esize = SIZE_STACK (solver->original) - offset;
    int *elits = BEGIN_STACK (solver->original) + offset;
    assert (esize <= UINT_MAX);
#endif
    ADD_UNCHECKED_EXTERNAL (esize, elits);
    const size_t isize = SIZE_STACK (solver->clause);
    unsigned *ilits = BEGIN_STACK (solver->clause);
    assert (isize < (unsigned) INT_MAX);

    if (solver->inconsistent)
      LOG ("inconsistent thus skipping original clause");
    else if (solver->clause_satisfied)
      LOG ("skipping satisfied original clause");
    else if (solver->clause_trivial)
      LOG ("skipping trivial original clause");
    else {
      kissat_activate_literals (solver, isize, ilits);

      if (!isize) {
        if (solver->clause_shrink)
          LOG ("all original clause literals root level falsified");
        else
          LOG ("found empty original clause");

        if (!solver->inconsistent) {
          LOG ("thus solver becomes inconsistent");
          solver->inconsistent = true;
          CHECK_AND_ADD_EMPTY ();
          ADD_EMPTY_TO_PROOF ();
        }
      } else if (isize == 1) {
        unsigned unit = TOP_STACK (solver->clause);

        if (solver->clause_shrink)
          LOGUNARY (unit, "original clause shrinks to");
        else
          LOGUNARY (unit, "found original");

        // A newly added permanent unit can contradict a retained decision.
        if (solver->level)
          kissat_backtrack_in_consistent_state (solver, 0);
        kissat_original_unit (solver, unit);

        COVER (solver->level);
        if (!solver->level)
          (void) kissat_search_propagate (solver);
      } else {
        reference res = kissat_new_original_clause (solver);

        const unsigned a = ilits[0];
        const unsigned b = ilits[1];

        const value u = VALUE (a);
        const value v = VALUE (b);

        const unsigned k = u ? LEVEL (a) : UINT_MAX;
        const unsigned l = v ? LEVEL (b) : UINT_MAX;

        bool assign = false;

        if (!u && v < 0) {
          LOG ("original clause immediately forcing");
          assign = true;
        } else if (u < 0 && k == l) {
          LOG ("both watches falsified at level @%u", k);
          assert (v < 0);
          assert (k > 0);
          kissat_backtrack_without_updating_phases (solver, k - 1);
        } else if (u < 0) {
          LOG ("watches falsified at levels @%u and @%u", k, l);
          assert (v < 0);
          assert (k > l);
          assert (l > 0);
          kissat_backtrack_in_consistent_state (solver, l);
          assign = true;
        } else if (u > 0 && v < 0) {
          LOG ("first watch satisfied at level @%u "
               "second falsified at level @%u",
               k, l);
          if (k > l) {
            kissat_backtrack_in_consistent_state (solver, l);
            assign = true;
          }
        }

        if (assign) {
          assert (solver->level > 0);

          if (isize == 2) {
            assert (res == INVALID_REF);
            kissat_assign_binary (solver, a, b);
          } else {
            assert (res != INVALID_REF);
            clause *c = kissat_dereference_clause (solver, res);
            kissat_assign_reference (solver, a, res, c);
          }
        }
      }
    }

#if !defined(NDEBUG) || !defined(NPROOFS)
    if (solver->clause_satisfied || solver->clause_trivial) {
#ifndef NDEBUG
      if (checking > 1)
        kissat_remove_checker_external (solver, esize, elits);
#endif
#ifndef NPROOFS
      if (proving) {
        if (esize == 1)
          LOG ("skipping deleting unit from proof");
        else
          kissat_delete_external_from_proof (solver, esize, elits);
      }
#endif
    } else if (!solver->inconsistent && solver->clause_shrink) {
#ifndef NDEBUG
      if (checking > 1) {
        kissat_check_and_add_internal (solver, isize, ilits);
        kissat_remove_checker_external (solver, esize, elits);
      }
#endif
#ifndef NPROOFS
      if (proving) {
        kissat_add_lits_to_proof (solver, isize, ilits);
        kissat_delete_external_from_proof (solver, esize, elits);
      }
#endif
    }
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    if (checking) {
      LOGINTS (esize, elits, "saved original");
      PUSH_STACK (solver->original, 0);
      solver->offset_of_last_original_clause =
          SIZE_STACK (solver->original);
    } else if (logging || proving) {
      LOGINTS (esize, elits, "reset original");
      CLEAR_STACK (solver->original);
      solver->offset_of_last_original_clause = 0;
    }
#endif
    for (all_stack (unsigned, lit, solver->clause))
      MARK (lit) = MARK (NOT (lit)) = 0;

    CLEAR_STACK (solver->clause);

    solver->clause_satisfied = false;
    solver->clause_trivial = false;
    solver->clause_shrink = false;
  }
}

// Restore the complete extension when a caller revisits an eliminated
// variable. incremental=1 already makes BVE and substitution record both
// polarities, so these are clauses of the permanent formula, not a chosen
// witness. Learned clauses and the remaining CNF survive the restoration.
static void restore_eliminated (kissat *solver) {
  if (EMPTY_STACK (solver->eliminated))
    return;
  if (solver->level)
    kissat_backtrack_in_consistent_state (solver, 0);
  START (restore);
  INC (incremental_restorations);
  ADD (incremental_restored_literals, SIZE_STACK (solver->extend));
  extensions restore = solver->extend;
  INIT_STACK (solver->extend);
  CLEAR_STACK (solver->etrail);
  CLEAR_STACK (solver->eliminated);
  // The old internal identities remain inactive until collection. Detach
  // their exports before the same external IDs acquire fresh identities;
  // otherwise compaction maps an old slot to a newer, larger slot.
  for (all_variables (idx))
    if (FLAGS (idx)->eliminated)
      POKE_STACK (solver->export, idx, 0);
  const size_t size = SIZE_STACK (solver->import);
  for (unsigned eidx = 1; eidx < size; eidx++) {
    import *import = &PEEK_STACK (solver->import, eidx);
    if (!import->eliminated)
      continue;
    const bool extension = import->extension;
    import->eliminated = false;
    import->imported = false;
    (void) kissat_import_literal (solver, (int) eidx);
    // Importing can enlarge the tables. Reacquire the pointer afterwards.
    PEEK_STACK (solver->import, eidx).extension = extension;
  }
  bool clause = false;
  for (all_stack (extension, ext, restore)) {
    if (ext.blocking && clause)
      add_original (solver, 0);
    add_original (solver, ext.lit);
    clause = true;
  }
  if (clause)
    add_original (solver, 0);
  RELEASE_STACK (restore);
  STOP (restore);
}

static void prepare_incremental (kissat *solver) {
  solver->extended = false;
  if (solver->level &&
      (!GET_OPTION (incrementalreuse) || !solver->reusable))
    kissat_backtrack_in_consistent_state (solver, 0);
  solver->result = 0;
}

static bool eliminated_external (kissat *solver, int elit) {
  const unsigned eidx = ABS (elit);
  return eidx < SIZE_STACK (solver->import) &&
         PEEK_STACK (solver->import, eidx).eliminated;
}

void kissat_add (kissat *solver, int elit) {
  kissat_require_initialized (solver);
  if (!GET_OPTION (incremental)) {
    kissat_require (!solver->solve_calls,
                    "enable incremental before adding clauses after solve");
    add_original (solver, elit);
    return;
  }
  // Before the first solve no variable has been eliminated and no trail
  // needs repair. Stream the initial CNF through the original import path.
  if (!solver->solve_calls) {
    add_original (solver, elit);
    return;
  }
  if (elit) {
    kissat_require_valid_external_internal (elit);
    PUSH_STACK (solver->pending, elit);
  } else {
    prepare_incremental (solver);
    for (all_stack (int, lit, solver->pending))
      if (eliminated_external (solver, lit)) {
        restore_eliminated (solver);
        break;
      }
    for (all_stack (int, lit, solver->pending))
      add_original (solver, lit);
    add_original (solver, 0);
    CLEAR_STACK (solver->pending);
  }
}

void kissat_protect (kissat *solver, int elit) {
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (elit);
  kissat_require (GET_OPTION (incremental), "enable incremental first");
  kissat_require (EMPTY_STACK (solver->pending) &&
                  EMPTY_STACK (solver->clause), "incomplete clause");
  prepare_incremental (solver);
  if (eliminated_external (solver, elit))
    restore_eliminated (solver);
  const unsigned ilit = kissat_import_literal (solver, elit);
  if (!FLAGS (IDX (ilit))->fixed)
    kissat_activate_literal (solver, ilit);
  import *import = &PEEK_STACK (solver->import, ABS (elit));
  kissat_require (import->protected < UINT_MAX, "protection count overflow");
  import->protected++;
}

void kissat_unprotect (kissat *solver, int elit) {
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (elit);
  const unsigned eidx = ABS (elit);
  kissat_require (eidx < SIZE_STACK (solver->import) &&
                  PEEK_STACK (solver->import, eidx).protected,
                  "variable %u is not protected", eidx);
  PEEK_STACK (solver->import, eidx).protected--;
}

void kissat_assume (kissat *solver, int elit) {
  kissat_protect (solver, elit);
  PUSH_STACK (solver->assumptions, elit);
}

int kissat_failed (kissat *solver, int elit) {
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (elit);
  if (solver->result != 20)
    return 0;
  for (all_stack (int, lit, solver->failed))
    if (lit == elit)
      return 1;
  return 0;
}

int kissat_inconsistent (kissat *solver) {
  kissat_require_initialized (solver);
  return solver->inconsistent;
}

int kissat_maximum_variable (kissat *solver) {
  kissat_require_initialized (solver);
  const size_t size = SIZE_STACK (solver->import);
  return size ? (int) (size - 1) : 0;
}

void kissat_set_phase (kissat *solver, int elit) {
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (elit);
  const unsigned eidx = ABS (elit);
  if (eidx >= SIZE_STACK (solver->import))
    return;
  const import *import = &PEEK_STACK (solver->import, eidx);
  if (!import->imported || import->eliminated)
    return;
  unsigned ilit = import->lit;
  if (elit < 0)
    ilit = NOT (ilit);
  SAVED (IDX (ilit)) = NEGATED (ilit) ? -1 : 1;
}

int kissat_solve (kissat *solver) {
  kissat_require_initialized (solver);
  kissat_require (EMPTY_STACK (solver->clause) &&
                  EMPTY_STACK (solver->pending),
                  "incomplete clause (terminating zero not added)");
  kissat_require (!solver->solve_calls || GET_OPTION (incremental),
                  "enable incremental before repeated solving");
  prepare_incremental (solver);
  CLEAR_STACK (solver->failed);
  const size_t previous = SIZE_STACK (solver->previous_assumptions);
  const size_t current = SIZE_STACK (solver->assumptions);
  size_t common = 0;
  while (common < previous && common < current &&
         PEEK_STACK (solver->previous_assumptions, common) ==
             PEEK_STACK (solver->assumptions, common))
    common++;
  unsigned keep = 0;
  size_t consumed = 0;
  const bool all = GET_OPTION (incrementalreuse) == 2 &&
                   solver->reusable && solver->assumptions_complete &&
                   common == previous &&
                   common == current &&
                   solver->level >= SIZE_STACK (solver->assumption_decisions);
  if (all) {
    keep = solver->level;
    consumed = current;
  } else if (GET_OPTION (incrementalreuse) && solver->reusable) {
    const size_t decisions = SIZE_STACK (solver->assumption_decisions);
    for (; keep < solver->level && keep < decisions; keep++) {
      const int elit = PEEK_STACK (solver->assumption_decisions, keep);
      size_t pos = consumed;
      while (pos < common &&
             PEEK_STACK (solver->assumptions, pos) != elit)
        pos++;
      if (pos == common)
        break;
      consumed = pos + 1;
    }
  }
  if (solver->level > keep)
    kissat_backtrack_in_consistent_state (solver, keep);
  if (keep) {
    INC (incremental_reused_solves);
    ADD (incremental_reused_levels, keep);
  }
  if (!all)
    RESIZE_STACK (solver->assumption_decisions, keep);
  solver->assumption_next = consumed;
  const int res = kissat_search (solver);
  if (res == 20 && !solver->inconsistent && EMPTY_STACK (solver->failed))
    for (all_stack (int, lit, solver->assumptions))
      PUSH_STACK (solver->failed, lit);
  for (all_stack (int, lit, solver->assumptions))
    kissat_unprotect (solver, lit);
  CLEAR_STACK (solver->previous_assumptions);
  for (all_stack (int, lit, solver->assumptions))
    PUSH_STACK (solver->previous_assumptions, lit);
  solver->assumptions_complete = solver->assumption_next == current;
  CLEAR_STACK (solver->assumptions);
  solver->assumption_next = 0;
  solver->reusable = res == 10 || res == 0;
  solver->solve_calls++;
  solver->result = res;
  // Early preprocessing/lucky exits do not pass through stop_search.
  solver->limited.conflicts = solver->limited.decisions = false;
  solver->termination.flagged = 0;
  return res;
}

void kissat_terminate (kissat *solver) {
  kissat_require_initialized (solver);
#ifdef COVERAGE
  solver->termination.flagged = ~(uint64_t) 0;
#else
  solver->termination.flagged = ~(unsigned) 0;
#endif
  assert (solver->termination.flagged);
}

void kissat_set_terminate (kissat *solver, void *state,
                           int (*terminate) (void *)) {
  solver->termination.terminate = 0;
  solver->termination.state = state;
  solver->termination.terminate = terminate;
}

int kissat_value (kissat *solver, int elit) {
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (elit);
  const unsigned eidx = ABS (elit);
  if (eidx >= SIZE_STACK (solver->import))
    return 0;
  const import *const import = &PEEK_STACK (solver->import, eidx);
  if (!import->imported)
    return 0;
  value tmp;
  if (import->eliminated) {
    if (!solver->extended && !EMPTY_STACK (solver->extend))
      kissat_extend (solver);
    const unsigned eliminated = import->lit;
    tmp = PEEK_STACK (solver->eliminated, eliminated);
  } else {
    const unsigned ilit = import->lit;
    tmp = VALUE (ilit);
  }
  if (!tmp)
    return 0;
  if (elit < 0)
    tmp = -tmp;
  return tmp < 0 ? -elit : elit;
}
