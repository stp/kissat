#ifndef _kitten_h_INCLUDED
#define _kitten_h_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

// CaDiCaL embeds another Kitten with the same API. Keep these symbols
// separate when both SAT solvers are linked into one application.
#ifndef STAND_ALONE_KITTEN
#define kitten_assume kissat_kitten_assume
#define kitten_binary kissat_kitten_binary
#define kitten_clause kissat_kitten_clause
#define kitten_clause_with_id_and_exception kissat_kitten_clause_with_id_and_exception
#define kitten_clear kissat_kitten_clear
#define kitten_compute_clausal_core kissat_kitten_compute_clausal_core
#define kitten_embedded kissat_kitten_embedded
#define kitten_failed kissat_kitten_failed
#define kitten_fixed kissat_kitten_fixed
#define kitten_flip_literal kissat_kitten_flip_literal
#define kitten_flip_phases kissat_kitten_flip_phases
#define kitten_init kissat_kitten_init
#define kitten_no_ticks_limit kissat_kitten_no_ticks_limit
#define kitten_randomize_phases kissat_kitten_randomize_phases
#define kitten_release kissat_kitten_release
#define kitten_set_ticks_limit kissat_kitten_set_ticks_limit
#define kitten_shrink_to_clausal_core kissat_kitten_shrink_to_clausal_core
#define kitten_shuffle_clauses kissat_kitten_shuffle_clauses
#define kitten_solve kissat_kitten_solve
#define kitten_status kissat_kitten_status
#define kitten_track_antecedents kissat_kitten_track_antecedents
#define kitten_traverse_core_clauses kissat_kitten_traverse_core_clauses
#define kitten_traverse_core_ids kissat_kitten_traverse_core_ids
#define kitten_unit kissat_kitten_unit
#define kitten_value kissat_kitten_value
#endif

typedef struct kitten kitten;

kitten *kitten_init (void);
void kitten_clear (kitten *);
void kitten_release (kitten *);

void kitten_track_antecedents (kitten *);

void kitten_shuffle_clauses (kitten *);
void kitten_flip_phases (kitten *);
void kitten_randomize_phases (kitten *);

void kitten_assume (kitten *, unsigned lit);

void kitten_clause (kitten *, size_t size, unsigned *);
void kitten_unit (kitten *, unsigned);
void kitten_binary (kitten *, unsigned, unsigned);

void kitten_clause_with_id_and_exception (kitten *, unsigned id,
                                          size_t size, const unsigned *,
                                          unsigned except);

void kitten_no_ticks_limit (kitten *);
void kitten_set_ticks_limit (kitten *, uint64_t);

int kitten_solve (kitten *);
int kitten_status (kitten *);

signed char kitten_value (kitten *, unsigned);
signed char kitten_fixed (kitten *, unsigned);
bool kitten_failed (kitten *, unsigned);
bool kitten_flip_literal (kitten *, unsigned);

unsigned kitten_compute_clausal_core (kitten *, uint64_t *learned);
void kitten_shrink_to_clausal_core (kitten *);

void kitten_traverse_core_ids (kitten *, void *state,
                               void (*traverse) (void *state, unsigned id));

void kitten_traverse_core_clauses (kitten *, void *state,
                                   void (*traverse) (void *state,
                                                     bool learned, size_t,
                                                     const unsigned *));
struct kissat;
kitten *kitten_embedded (struct kissat *);

#endif
