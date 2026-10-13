#ifndef _incremental_h_INCLUDED
#define _incremental_h_INCLUDED

#include "internal.h"

static inline bool kissat_assuming (kissat *solver) {
  return solver->level < SIZE_STACK (solver->assumption_decisions) ||
         solver->assumption_next < SIZE_STACK (solver->assumptions);
}

int kissat_assign_assumption (kissat *solver);

#endif
