// EXPECT: VERIFICATION FAILED under --rounds; g rejected with "2 roots".
// Exercises transitive (6 levels deep) call-graph reachability.
//
// NEW ADVERSARIAL: the second thread touches g six calls deep.
#include <pthread.h>
#include <assert.h>
int g = 0;
void f6(void) { g = 99; }
void f5(void) { f6(); }
void f4(void) { f5(); }
void f3(void) { f4(); }
void f2(void) { f3(); }
void f1(void) { f2(); }
void *t2(void *arg) { f1(); return 0; }
void *t1(void *arg) { for(g = 0; g < 2; g++) {} assert(g == 2); return 0; }
int main() {
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0); pthread_join(b, 0);
  return 0;
}
