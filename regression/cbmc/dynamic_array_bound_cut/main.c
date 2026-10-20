#include <stdlib.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int main() { int n = __VERIFIER_nondet_int(); if (n < 1 || n > 8) return 0;
  int *a = malloc(n * sizeof(int));
  a[0] = 1; if (n == 6) reach_error();
  return 0; }
