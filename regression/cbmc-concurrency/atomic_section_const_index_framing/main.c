#include <pthread.h>
int arr[2];
int other[2];
void checkInv() {
  __CPROVER_assert(other[0] <= arr[0] && other[1] <= arr[1], "invariant");
}
void bump(int idx) {
  __VERIFIER_atomic_begin();
  arr[idx]++;
  checkInv();
  __VERIFIER_atomic_end();
}
void *w0(void *a) { bump(1); return 0; }
void *w1(void *a) { bump(1); return 0; }
int main() {
  arr[0] = 0; arr[1] = 0; other[0] = 0; other[1] = 0;
  pthread_t t0, t1;
  pthread_create(&t0, 0, w0, 0);
  pthread_create(&t1, 0, w1, 0);
  pthread_join(t0, 0);
  pthread_join(t1, 0);
  return 0;
}
