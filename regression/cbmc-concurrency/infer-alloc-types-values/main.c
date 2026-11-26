// Bytes past the struct (the block is larger than the struct) keep their values,
// and a field written through a char pointer reads back through the struct.
#include <stdlib.h>
#include <assert.h>
struct s { int a; int *p; };
void *my_alloc(unsigned long n) { void *r = malloc(n); __CPROVER_assume(r != 0); return r; }
int x;
int main(void)
{
  void *tmp;
  tmp = my_alloc(13UL);
  struct s *q = (struct s *)tmp;
  char *c = (char *)tmp;
  c[sizeof(struct s) + 1] = 42;
  q->p = &x;
  c[0] = 7; c[1] = 0; c[2] = 0; c[3] = 0;
  assert(c[sizeof(struct s) + 1] == 42);
  assert(q->a == 7);
  *q->p = 5;
  assert(x == 5);
  assert(q->a == 8); // must fail
  return 0;
}
