#include <stdlib.h>
#include <string.h>
#include <pthread.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern unsigned __VERIFIER_nondet_uint(void);
int main(){ int n = __VERIFIER_nondet_int(); if (n < 1 || n > 3) return 0; int i = __VERIFIER_nondet_int(); if (i < 0 || i >= 2*n) return 0;
  int *a = malloc(2 * n * sizeof(int)); a[i] = 55; if (a[i] != 55) reach_error(); return 0; }
