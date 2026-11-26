// Two threads store 1 into two (possibly different) symbolically indexed
// elements of the same array. Neither store can undo the other, so a[gi] is 1
// once both threads have joined.
//
// Before the framed-write fix each thread published a write to *every* element
// carrying the value it read at the start of its store, so whichever thread
// wrote second reset the other element -- a lost update that only ever existed
// in the encoding.
#include <pthread.h>

extern int __VERIFIER_nondet_int();

int a[4];
int gi, gj;

void *T1(void *x)
{
  a[gi] = 1;
  return 0;
}
void *T2(void *x)
{
  a[gj] = 1;
  return 0;
}

int main()
{
  gi = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= gi && gi < 4);
  gj = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= gj && gj < 4);
  pthread_t t1, t2;
  pthread_create(&t1, 0, T1, 0);
  pthread_create(&t2, 0, T2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  __CPROVER_assert(a[gi] == 1, "no lost update");
  return 0;
}
