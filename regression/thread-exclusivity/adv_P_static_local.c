// EXPECT: VERIFICATION FAILED under --rounds; bump::1::s rejected with
// "2 roots". Function-local statics are static-lifetime shared symbols and
// must be counted like any other global.
//
// NEW ADVERSARIAL: the shared state is a FUNCTION-LOCAL static in a helper
// called from two threads.
#include <pthread.h>
#include <assert.h>
int bump(int set99) { static int s = 0; if(set99) s = 99; else s++; return s; }
void *t1(void *arg) {
  int v = 0;
  while(v < 2) v = bump(0);
  assert(v == 2);
  return 0;
}
void *t2(void *arg) { bump(1); return 0; }
int main() {
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0); pthread_join(b, 0);
  return 0;
}
