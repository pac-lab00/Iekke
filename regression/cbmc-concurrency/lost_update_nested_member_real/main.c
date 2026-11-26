// Thread 1 stores member f, thread 2 member g, of the same element of an
// array of structs, both at a computed index. Both stores must survive.
#include <pthread.h>
struct I { int f; int g; };
struct S { int h; struct I s; };
struct S a[4];
unsigned idx;
void *t1(void *arg) { unsigned i = idx; a[i].s.f = a[i].s.f + 1; return 0; }
void *t2(void *arg) { unsigned j = idx; a[j].s.f = a[j].s.f + 1; return 0; }
int main()
{
  idx = __VERIFIER_nondet_uint();
  __CPROVER_assume(idx < 4);
  pthread_t x, y;
  pthread_create(&x, 0, t1, 0);
  pthread_create(&y, 0, t2, 0);
  pthread_join(x, 0);
  pthread_join(y, 0);
  __CPROVER_assert(a[idx].s.f == 2, "both members survive");
  return 0;
}
