#ifndef _exchange_h_INCLUDED
#define _exchange_h_INCLUDED

#include "kissat.h"
#include "stack.h"

#include <stdbool.h>
#include <stdint.h>

// Learned-clause exchange between copies of one loaded solver, and search
// diversification of such a copy (STP extensions, see 'exchange.c').

typedef struct exchange exchange;

struct exchange {
  void *learn_state;
  void (*learn) (void *state, unsigned size, const int *clause);
  unsigned max_size;

  void *import_state;
  unsigned (*budget) (void *state);
  const int *(*next) (void *state, unsigned *size);
  unsigned interval;
  uint64_t limit;

  kissat_import_statistics statistics;
  ints exported;
  unsigneds accepted;
};

struct kissat;

void kissat_export_clause (struct kissat *, unsigned size,
                           const unsigned *lits);
int kissat_import_clauses (struct kissat *);
void kissat_release_exchange (struct kissat *);

#endif
