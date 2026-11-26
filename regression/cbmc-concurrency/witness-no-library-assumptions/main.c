#include <stdlib.h>
extern int e;
int nondet_int();
int main()
{
  int x = nondet_int();
  int *p = malloc(sizeof(int));
  if(x + e == 3)
    p = 0;
  free(p);
  return 0;
}
