#ifndef _kissat_h_INCLUDED
#define _kissat_h_INCLUDED

#define KISSAT_HAS_INCREMENTAL 1
#define KISSAT_HAS_INTERRUPTIBLE_LUCKY 1
#define KISSAT_HAS_INCREMENTAL_GREEDY 1
#define KISSAT_HAS_CLAUSE_EXCHANGE 1
#define KISSAT_HAS_EXTERNAL_PROPAGATOR 1

#include <stddef.h>
#include <stdint.h>

typedef struct kissat_allocator {
  void *state;
  void *(*allocate) (void *state, size_t bytes);
  void *(*resize) (void *state, void *ptr, size_t bytes);
  void (*deallocate) (void *state, void *ptr);
} kissat_allocator;

// Allocation callbacks must return valid storage or exit nonlocally. After
// a nonlocal exit the owner must reclaim all blocks and discard the solver;
// its partially modified structures cannot be passed to kissat_release.

typedef struct kissat kissat;

// Default (partial) IPASIR interface.

const char *kissat_signature (void);
kissat *kissat_init (void);
kissat *kissat_init_with_allocator (const kissat_allocator *allocator);
void kissat_add (kissat *solver, int lit);
void kissat_assume (kissat *solver, int lit);
int kissat_failed (kissat *solver, int lit);
void kissat_protect (kissat *solver, int var);
void kissat_unprotect (kissat *solver, int var);
int kissat_solve (kissat *solver);
int kissat_value (kissat *solver, int lit);
int kissat_inconsistent (kissat *solver);
int kissat_maximum_variable (kissat *solver);
void kissat_set_phase (kissat *solver, int lit);
void kissat_release (kissat *solver);

void kissat_set_terminate (kissat *solver, void *state,
                           int (*terminate) (void *state));

// Additional API functions.

void kissat_terminate (kissat *solver);
void kissat_reserve (kissat *solver, int max_var);

const char *kissat_id (void);
const char *kissat_version (void);
const char *kissat_compiler (void);

const char **kissat_copyright (void);
void kissat_build (const char *line_prefix);
void kissat_banner (const char *line_prefix, const char *name_of_app);

int kissat_get_option (kissat *solver, const char *name);
int kissat_set_option (kissat *solver, const char *name, int new_value);

void kissat_set_prefix (kissat *solver, const char *prefix);

int kissat_has_configuration (const char *name);
int kissat_set_configuration (kissat *solver, const char *name);

void kissat_set_conflict_limit (kissat *solver, unsigned);
void kissat_set_decision_limit (kissat *solver, unsigned);

void kissat_print_statistics (kissat *solver);

// Learned-clause exchange between copies of one loaded solver, for example
// processes forked after the clauses were added (an STP extension).
//
// After 'kissat_set_learn', every clause of at most 'max_size' literals
// that conflict analysis learns, and every unit derived at the root, is
// passed to 'learn' in external literals, from inside the search. A clause
// over a variable the solver introduced itself ('factor') is not passed on.
// A zero 'learn' disconnects.
//
// After 'kissat_set_import', the search calls 'next' between propagation
// and the next decision, once every 'interval' conflicts. Such a poll
// starts with 'budget' (if given), which returns how many clauses of two or
// more literals it accepts (units are never limited), and ends at the first
// 'next' that returns zero. Otherwise 'next' returns the external literals
// of one clause, valid until its next call, and stores their number in
// 'size'. Every clause must be implied by the clauses added to this solver;
// it is added as a redundant clause. A clause naming a variable that is not
// active here (eliminated, substituted, unused or introduced by the solver)
// is dropped, as is everything while a proof is written. A zero 'next'
// disconnects. Neither callback may call back into the solver.

void kissat_set_learn (kissat *solver, void *state, unsigned max_size,
                       void (*learn) (void *state, unsigned size,
                                      const int *clause));

void kissat_set_import (kissat *solver, void *state, unsigned interval,
                        unsigned (*budget) (void *state),
                        const int *(*next) (void *state, unsigned *size));

typedef struct kissat_import_statistics {
  uint64_t polls, clauses, units, dropped, satisfied, backtracks;
} kissat_import_statistics;

void kissat_get_import_statistics (kissat *solver,
                                   kissat_import_statistics *statistics);

// Search diversification of a solver that already holds clauses, between
// solves: the random seed, every saved phase ('phase' 1 true, -1 false, 0
// pseudo-random from 'seed', any other value keeps them), and with
// 'shuffle' the order of the decision queue and the scores. Nothing else
// changes, so copies of one solver search differently on the same clauses.

void kissat_diversify (kissat *solver, int seed, int phase, int shuffle);

// External propagation, the IPASIR-UP interface (an STP extension), with
// CaDiCaL's callbacks as C function pointers and the decision polarity
// advice of STP's CaDiCaL fork. Requires the 'incremental' option and no
// proof. The callbacks run inside 'kissat_solve' and must not call back
// into the solver, except 'kissat_is_decision'.
//
// The propagator is told, in trail order, every assignment of an observed
// variable ('notify_assignment'), every new decision level and every
// backtrack below a level it heard about. Root assignments are told at the
// root, a variable fixed before it was observed included, and an assignment
// that chronological backtracking keeps is told again. 'check_found_model'
// accepts (nonzero) or rejects a complete assignment, given as the values
// of the observed variables; after a rejection 'has_external_clause' must
// offer a clause that the assignment falsifies. 'has_external_clause' is
// asked after every propagation fixpoint; its clauses, read literal by
// literal with 'add_external_clause_lit' up to a zero, may only name active
// (or fixed) variables, and are redundant when it sets 'is_forgettable'.
// The optional 'propagate' returns an implied literal of an observed
// variable, or zero, and 'add_reason_clause_lit' then reads its reason
// clause, which contains it. The optional 'decide' returns an unassigned
// literal of an observed variable to decide, or zero. The optional
// 'advise_decision_polarity' sees the literal the ordinary heuristic is
// about to decide, for observed variables only, and returns it, its
// negation or zero (keep it).
//
// Observing a variable protects it from elimination and substitution
// (restoring it first if necessary). Disconnecting unobserves everything.

typedef struct kissat_external_propagator {
  void *state;
  void (*notify_assignment) (void *state, const int *lits, size_t size);
  void (*notify_new_decision_level) (void *state);
  void (*notify_backtrack) (void *state, size_t new_level);
  int (*check_found_model) (void *state, const int *model, size_t size);
  int (*has_external_clause) (void *state, int *is_forgettable);
  int (*add_external_clause_lit) (void *state);
  int (*propagate) (void *state);
  int (*add_reason_clause_lit) (void *state, int propagated_lit);
  int (*decide) (void *state);
  int (*advise_decision_polarity) (void *state, int default_literal);
} kissat_external_propagator;

void kissat_connect_external_propagator (
    kissat *solver, const kissat_external_propagator *propagator);
void kissat_disconnect_external_propagator (kissat *solver);
void kissat_add_observed_var (kissat *solver, int var);
void kissat_remove_observed_var (kissat *solver, int var);
void kissat_reset_observed_vars (kissat *solver);
int kissat_is_decision (kissat *solver, int lit);

#endif
