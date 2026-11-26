#include <pthread.h>
#include <stdlib.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int *a; int n; int k; int done;
void *t(void *x) { char *c = (char *)a; c[k] = 1; done = 1; return 0; }
int main() { n = __VERIFIER_nondet_int(); if (n < 4 || n > 8) return 0; a = malloc(n * sizeof(int)); a[0] = 0; a[1] = 0; a[2] = 0; a[3] = 0;
  k = __VERIFIER_nondet_int(); if (k < 0 || k > 15) return 0;
  pthread_t h; pthread_create(&h, 0, t, 0);
  if (!done) return 0; /* the thread's write came first */
  char *c = (char *)a; c[k] = 2;
  pthread_join(h, 0);
  if (k == 5 && a[1] != 512) reach_error();
  return 0; }
