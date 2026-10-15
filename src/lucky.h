#ifndef _lucky_h_INCLUDED
#define _lucky_h_INCLUDED

struct kissat;
int kissat_lucky (struct kissat *);
int kissat_assumption_lucky (struct kissat *, unsigned mode);

#endif
