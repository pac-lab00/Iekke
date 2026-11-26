// Two threads store to different elements of an int array at computed
// indices: no data race.
#include <pthread.h>
struct I { int f; int g; };
struct S { int h; struct I s; };
struct S a[4];
unsigned i0, j0;
void *t1(void *arg) { a[i0].s.f = 1; return 0; }
void *t2(void *arg) { a[j0].s.g = 2; return 0; }
int main()
{
  i0 = __VERIFIER_nondet_uint(); j0 = __VERIFIER_nondet_uint();
  __CPROVER_assume(i0 < 4 && j0 < 4);
  pthread_t x, y;
  pthread_create(&x, 0, t1, 0);
  pthread_create(&y, 0, t2, 0);
  pthread_join(x, 0);
  pthread_join(y, 0);
  return 0;
}
