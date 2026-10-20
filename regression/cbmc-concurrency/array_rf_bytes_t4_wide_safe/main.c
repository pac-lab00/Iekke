#include <pthread.h>
#include <stdlib.h>
#include <string.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int *a; int n; int k; int dummy;
void *t(void *x) { char *c = (char *)a; c[4+k] = 2; a[0] = 3; return 0; }
int main() { n = __VERIFIER_nondet_int(); if (n < 4 || n > 8) return 0; a = malloc(n * sizeof(int)); a[0] = 0; a[1] = 0; a[2] = 0; a[3] = 0; k = __VERIFIER_nondet_int(); if (k < 0 || k > 3) return 0; pthread_t h; pthread_create(&h, 0, t, 0); dummy = 1; pthread_join(h, 0); long long v = *(long long *)a; if (k == 0 && v != (2LL<<32) + 3) reach_error(); return 0; }
