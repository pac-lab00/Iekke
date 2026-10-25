// One thread reads member f, the other stores member g, of the same element
// at a computed index: different memory locations, no data race.
#include <pthread.h>
struct S { int f; int g; };
struct S a[4];
unsigned i0;
int x;
void *t1(void *arg) { x = a[i0].f; return 0; }
void *t2(void *arg) { a[i0].g = 2; return 0; }
int main()
{
  i0 = __VERIFIER_nondet_uint();
  __CPROVER_assume(i0 < 4);
  pthread_t p, q;
  pthread_create(&p, 0, t1, 0);
  pthread_create(&q, 0, t2, 0);
  pthread_join(p, 0);
  pthread_join(q, 0);
  return 0;
}
