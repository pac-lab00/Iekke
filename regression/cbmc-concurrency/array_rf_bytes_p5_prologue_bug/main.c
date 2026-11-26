#include <pthread.h>
#include <stdlib.h>
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "f.c", 1, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
int *a; int n; int k; int j; int dummy; short s; unsigned char r;
void *t(void *x) { unsigned char *c = (unsigned char *)a; s = *(short *)(c + 2 * j); r = c[j + k]; return 0; }
int main() {
  n = __VERIFIER_nondet_int(); if (n < 4 || n > 8) return 0;
  a = malloc(n * sizeof(int));
  k = __VERIFIER_nondet_int(); if (k < 0 || k > 3) return 0;
  j = __VERIFIER_nondet_int(); if (j < 0 || j > 3) return 0;
  unsigned char m[16]; unsigned char *c = (unsigned char *)a;
  a[0] = 0x11111111; m[0] = m[1] = m[2] = m[3] = 0x11;
  c[k] = 0x22; m[k] = 0x22;
  a[1] = 0x55555555; m[4] = m[5] = m[6] = m[7] = 0x55;
  *(short *)(c + 2 * k + 2) = 0x3344; m[2 * k + 2] = 0x44; m[2 * k + 3] = 0x33;
  a[2] = 0; m[8] = m[9] = m[10] = m[11] = 0;
  pthread_t h; pthread_create(&h, 0, t, 0); dummy = 1; pthread_join(h, 0);
  if (s != (short)(m[2 * j] | (m[2 * j + 1] << 8))) reach_error();
  if (j == 2 && k == 1 && s == 0x3344) reach_error();
  return 0;
}
