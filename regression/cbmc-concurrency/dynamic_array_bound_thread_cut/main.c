#include <stdlib.h>
#include <string.h>
#include <pthread.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
extern unsigned __VERIFIER_nondet_uint(void);
int x;
void *B(void *a){ int n = __VERIFIER_nondet_int(); if (n < 1 || n > 8) return 0; int *p = malloc(n * sizeof(int)); p[0] = 1; if (n == 6) reach_error(); return 0; }
int main(){ pthread_t b; pthread_create(&b,0,B,0); return 0; }
