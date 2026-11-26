#include <pthread.h>
int __VERIFIER_nondet_int(void);
void __VERIFIER_atomic_begin(void);
void __VERIFIER_atomic_end(void);
typedef struct C { struct C *n; int d; } C;
typedef struct T { unsigned id; int op; C cell; } T;
T th[4];
T *pa, *pb;
unsigned uid;
void *a(void *x) {
  __VERIFIER_atomic_begin();
  pa->id = ++uid;
  __VERIFIER_atomic_end();
  return 0;
}
int main(void) {
  int i = __VERIFIER_nondet_int(), j = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= i && i < 4 && 0 <= j && j < 4 && i == j);
  pa = &th[i]; pb = &th[j];
  pthread_t t;
  pthread_create(&t, 0, a, 0);
  pb->id = 0;
  pthread_join(t, 0);
  return 0;
}
