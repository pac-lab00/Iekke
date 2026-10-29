// The block is used through a second, unrelated struct type: values written
// through one type read back through the other byte for byte.
#include <stdlib.h>
#include <assert.h>
struct A { int x; int y; };
struct B { short h[4]; };
void *my_alloc(unsigned long n) { void *r = malloc(n); __CPROVER_assume(r != 0); return r; }
int main(void)
{
  void *tmp;
  tmp = my_alloc(8UL);
  struct A *a = (struct A *)tmp;
  struct B *b = (struct B *)tmp;
  a->y = 0x00030004;
  assert(b->h[2] == 4 && b->h[3] == 3);
  b->h[0] = 1; b->h[1] = 0;
  assert(a->x == 1);
  assert(a->y == 0x00030005); // must fail
  return 0;
}
