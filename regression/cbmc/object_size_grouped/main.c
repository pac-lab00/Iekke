#include <stdlib.h>
_Bool nondet_bool(void);
unsigned nondet_unsigned(void);
int a[3], b[3], c[5];
char s1;
struct { int x; char y[7]; } st;
int main(void)
{
  unsigned n = nondet_unsigned();
  __CPROVER_assume(n > 0 && n < 100);
  char *h = malloc(n);
  char *p;
  int k = nondet_unsigned() % 6;
  if(k == 0) p = (char *)a;
  else if(k == 1) p = (char *)b;
  else if(k == 2) p = (char *)c;
  else if(k == 3) p = &s1;
  else if(k == 4) p = (char *)&st;
  else p = h;
  unsigned sz = __CPROVER_OBJECT_SIZE(p);
  _Bool dyn = __CPROVER_DYNAMIC_OBJECT(p);
  __CPROVER_assert(k != 0 || (sz == 12 && !dyn), "a");
  __CPROVER_assert(k != 1 || (sz == 12 && !dyn), "b");
  __CPROVER_assert(k != 2 || (sz == 20 && !dyn), "c");
  __CPROVER_assert(k != 3 || (sz == 1 && !dyn), "s1");
  __CPROVER_assert(k != 4 || (sz == sizeof(st) && !dyn), "st");
  __CPROVER_assert(k != 5 || (sz == n && dyn), "heap");
  /* reachable: same size, different objects */
  __CPROVER_assert(!(sz == 12 && k == 1), "reach size 12 via b");
  __CPROVER_assert(!(dyn && sz == 42), "reach heap 42");
  return 0;
}
