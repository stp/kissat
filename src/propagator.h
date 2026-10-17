#ifndef _propagator_h_INCLUDED
#define _propagator_h_INCLUDED

#include "kissat.h"
#include "stack.h"

#include <stdbool.h>
#include <stdint.h>

// External propagation (IPASIR-UP, an STP extension, see 'propagator.c').

typedef struct propagator propagator;

struct propagator {
  kissat_external_propagator callbacks;
  bool connected;
  bool calling;            // inside a callback
  unsigned notified;       // trail position up to which it heard
  unsigned notified_level; // decision levels it heard about
  unsigned propagated;     // trail size when it last had nothing to say
  ints observed;           // external variables, in observation order
  chars observing;         // by external variable: observed or not
  ints fixed;              // root literals to notify before anything else
  ints notifications;      // the batch being told
  ints literals;           // model and clause scratch
  struct {
    uint64_t notified, propagated, clauses, conflicts, checks, rejected,
        decisions, advised, ignored;
  } statistics;
};

#define INVALID_PROPAGATED UINT_MAX

#define kissat_require_outside_callbacks(SOLVER) \
  kissat_require ( \
      !(SOLVER)->propagator.calling, \
      "can not call into the solver from a propagator callback")

struct kissat;

void kissat_release_propagator (struct kissat *);
void kissat_propagator_flush (struct kissat *);
void kissat_propagator_backtrack (struct kissat *, unsigned new_level,
                                  unsigned new_end);
int kissat_propagator_propagate (struct kissat *);
int kissat_propagator_check_model (struct kissat *);
bool kissat_propagator_decide (struct kissat *);
int kissat_propagator_advise (struct kissat *, unsigned idx, int value);

#endif
