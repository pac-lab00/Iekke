#include <stdlib.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int main() { int n = __VERIFIER_nondet_int(); if (n < 1 || n > 3) return 0;
  int *a = malloc(n * sizeof(int));
  a[n - 1] = 7; if (a[n - 1] == 7 && n == 3) reach_error();
  return 0; }
