#include <stdlib.h>
int nondet_int();
void reach_error()
{
}
int main()
{
  int *p = malloc(sizeof(int));
  free(p);
  if(nondet_int())
    free(p);
  unsigned char x = nondet_int();
  int y = x + 1;
  if(y > 256)
    reach_error();
  return 0;
}
