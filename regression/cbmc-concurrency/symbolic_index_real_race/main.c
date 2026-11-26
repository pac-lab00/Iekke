// Counterpart of symbolic_index_lost_update: here the lost update is one the
// program really performs (an unsynchronised read-modify-write of the same
// element by both threads), so it must still be reported. This pins down that
// suppressing *framed* element writes does not suppress genuine ones.
#include <pthread.h>

extern int __VERIFIER_nondet_int();

int a[4];
int gi;

void *T(void *x)
{
  int t = a[gi];
  a[gi] = t + 1;
  return 0;
}

int main()
{
  gi = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= gi && gi < 4);
  pthread_t t1, t2;
  pthread_create(&t1, 0, T, 0);
  pthread_create(&t2, 0, T, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  __CPROVER_assert(a[gi] == 2, "genuine lost update must still be found");
  return 0;
}
