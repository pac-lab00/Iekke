// With --yaml-witness-values the violation witness carries the values read
// from __VERIFIER_nondet_*, as function_return waypoints: a validator that
// executes the program (ConcurrentWitness2Test) otherwise runs it with inputs
// of its own (pthread-overflow/barrier-reuse-no-reset was confirmed only
// with them).
#include <pthread.h>
extern int __VERIFIER_nondet_int(void);
int x;
void *thr(void *arg)
{
  x = x + 1;
  return 0;
}
int main(void)
{
  pthread_t t;
  x = __VERIFIER_nondet_int();
  if(x < 2147483647)
    return 0;
  pthread_create(&t, 0, thr, 0);
  pthread_join(t, 0);
  return 0;
}
