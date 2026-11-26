#include <stdlib.h>
int nondet_int();

int main(void)
{
  int n = nondet_int();
  __CPROVER_assume(n >= 2 && n <= 4);
  int *a = malloc(sizeof(int) * n);
  __CPROVER_assume(a != 0);
  int i = nondet_int(), j = nondet_int();
  __CPROVER_assume(i >= 0 && i < n && j == i);
  a[i] = 5;
  __CPROVER_assert(a[j] == 5, "an index equal to the stored one reads the store");
  return 0;
}
