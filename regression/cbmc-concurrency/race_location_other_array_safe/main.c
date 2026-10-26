#include <pthread.h>
#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
int *A, *B; int AA[4], BB[4];
int M;
void *thread1(void *p) { B[0] = A[0]; return 0; }
void *thread3(void *p) { B[M] = A[M]; return 0; }
int main() {
  pthread_t t1, t3;
  M = __VERIFIER_nondet_int();
  if(!(M >= 1 && M < 4)) abort();
  A = AA;
  B = BB;
  if(!A || !B) abort();
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t3, 0, thread3, 0);
  pthread_join(t1, 0);
  pthread_join(t3, 0);
  return 0;
}
