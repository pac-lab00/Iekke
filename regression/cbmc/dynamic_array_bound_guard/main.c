#include <stdlib.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int main() { int n = __VERIFIER_nondet_int(); if (n < 5 || n > 8) return 0;
  int *a = malloc(n * sizeof(int));
  a[4] = 1; if (a[4] != 1) reach_error();
  return 0; }
