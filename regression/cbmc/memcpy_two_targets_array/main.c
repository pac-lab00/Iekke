// memcpy into an array member through a pointer with two possible targets:
// the element written before must keep its value in the target not reached.
#include <stdlib.h>
#include <string.h>
struct dev { int id; char buf[12]; };
int nondet_int(void);
int main()
{
  struct dev *a = malloc(sizeof(struct dev)), *b = malloc(sizeof(struct dev));
  if(!a || !b)
    return 0;
  a->buf[1] = 'e';
  struct dev *p = nondet_int() ? a : b;
  memcpy(p->buf + 8, "ab", 2);
  __CPROVER_assert(a->buf[1] == 'e', "an element the copy does not reach");
  return 0;
}
