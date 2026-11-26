#include <pthread.h>
int arr[2];
void bump(int idx) {
  __VERIFIER_atomic_begin();
  arr[idx]++;
  __VERIFIER_atomic_end();
}
void *w0(void *a) { bump(0); return 0; }
void *w1(void *a) { bump(0); return 0; }
int main() {
  arr[0] = 0; arr[1] = 0;
  pthread_t t0, t1;
  pthread_create(&t0, 0, w0, 0);
  pthread_create(&t1, 0, w1, 0);
  arr[0] = 9; /* unprotected: races with both threads' atomic bump(0) */
  pthread_join(t0, 0);
  pthread_join(t1, 0);
  return 0;
}
