#include <pthread.h>
#include <assert.h>
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);
int g;
int A[3];
void *t1(void *u) {
  int k = g + 2;
  __VERIFIER_atomic_begin();
  A[k]++;
  assert(A[0] == 0);
  __VERIFIER_atomic_end();
  return 0;
}
void *t2(void *u) { __VERIFIER_atomic_begin(); A[2]++; __VERIFIER_atomic_end(); return 0; }
int main() { g = 0; pthread_t a, b; pthread_create(&a, 0, t1, 0); pthread_create(&b, 0, t2, 0); return 0; }
