#include <pthread.h>
#include <stdlib.h>
#include <string.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int *a; int n; int k; int dummy;
int *b;
void *t(void *x) { char *c = (char *)(k & 1 ? a : b); c[k] = 1; return 0; }
int main() { n = __VERIFIER_nondet_int(); if (n < 4 || n > 8) return 0; a = malloc(n * sizeof(int)); a[0] = 0; a[1] = 0; a[2] = 0; a[3] = 0; k = __VERIFIER_nondet_int(); if (k < 0 || k > 3) return 0; b = malloc(n*sizeof(int)); b[0]=0; b[1]=0; pthread_t h; pthread_create(&h, 0, t, 0); dummy = 1; pthread_join(h, 0); if (k == 1 && a[0] != 256) reach_error(); if (k==0 && a[0] != 0) reach_error(); return 0; }
