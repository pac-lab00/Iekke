#include <pthread.h>
struct S { signed int f : 2; unsigned u : 3; };
_Atomic int ax;
void *t(void *a) { ax += 1; return 0; }
int main(void)
{
  struct S s = {1, 7};
  unsigned char c;
  int r1 = (c = 300);
  __CPROVER_assert(r1 == 44, "char assignment value");
  int r2 = (s.u += 2);
  __CPROVER_assert(r2 == 1, "unsigned bit-field compound value");
  int r3 = ++s.f;
  __CPROVER_assert(r3 == -2, "signed bit-field increment value");
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  int r4 = (ax += 1);
  pthread_join(id, 0);
  __CPROVER_assert(r4 == 1 || r4 == 2, "atomic rmw value");
  __CPROVER_assert(ax == 2, "atomic rmw no lost update");
  __CPROVER_assert(r4 != 2, "reach r4 == 2");
  return 0;
}
