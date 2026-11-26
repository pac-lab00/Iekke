#include <pthread.h>
#include <stdlib.h>
int nondet_int(void);
_Atomic int *A;
void *t(void *p) { A[0] = 1; return 0; }
int main() {
  int n = nondet_int(); __CPROVER_assume(1 <= n && n <= 3);
  A = malloc(n * sizeof(_Atomic int));
  if(A == 0) return 0;
  pthread_t h; pthread_create(&h, 0, t, 0); int r = A[0]; pthread_join(h, 0); return r;
}
