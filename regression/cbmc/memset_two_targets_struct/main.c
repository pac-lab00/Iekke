// memset through a pointer with two possible targets: the other object must
// keep its value.
#include <string.h>
struct P { int x; char c; short s; };
int nondet_int(void);
int main()
{
  struct P a = {1, 2, 3}, b = {4, 5, 6};
  struct P *q = nondet_int() ? &a : &b;
  memset(q, 0, sizeof(*q));
  __CPROVER_assert(q == &a ? b.x == 4 : a.x == 1, "the other target untouched");
  return 0;
}
