// A local array declared without an initialiser, shared with the threads.
//
// Its first version is defined by the declaration, not by an assignment, so
// --array-rf declined it and the whole array stayed on the chain: the goblint
// race_reach tasks declare `pthread_t t_ids[10000];`, and at u16 r4 that array
// was 99.8% of 181M clauses on race_reach_02. A declaration is now a write of
// nondeterministic contents: element j holds the declared version's own
// element j until written. So a[1], never written, is the same value at both
// reads, and is not known to be 0.

#include <pthread.h>

int *p;
int x, y;

void *t(void *arg)
{
  (void)arg;
  p[0] = 5;
  return 0;
}

void *u(void *arg)
{
  (void)arg;
  x = p[1];
  y = p[1];
  return 0;
}

int main(void)
{
  int a[1000];
  p = a;
  pthread_t ta, ua;
  pthread_create(&ta, 0, t, 0);
  pthread_create(&ua, 0, u, 0);
  pthread_join(ta, 0);
  pthread_join(ua, 0);
  __CPROVER_assert(x == y, "two reads of an element nobody wrote agree");
  return 0;
}
