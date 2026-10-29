// A store whose bytes all lie outside the struct it is resolved against
// must leave that struct unchanged.
#include <assert.h>
struct s { int a; int b; } x;
int main(void)
{
  x.a = 1;
  x.b = 2;
  char *p = (char *)&x + 100;
  *(int *)p = 5;
  assert(x.a == 1);
  assert(x.b == 2);
  assert(x.a == 7); // must fail
  return 0;
}
