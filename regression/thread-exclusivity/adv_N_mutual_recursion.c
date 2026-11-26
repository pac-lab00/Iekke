// EXPECT: VERIFICATION FAILED under --rounds; g rejected with "2 roots".
// Exercises reachable_from() over a call-graph cycle.
//
// NEW ADVERSARIAL: main touches g ONLY through a mutually-recursive chain
// aa <-> bb. If reachability fails to follow the cycle, g looks exclusive.
#include <pthread.h>
#include <assert.h>
int g = 0;
void bb(int n);
void aa(int n) { if(n > 0) bb(n - 1); }
void bb(int n) { if(n > 0) aa(n - 1); g = 99; }
void *t1(void *arg) { for(g = 0; g < 2; g++) {} assert(g == 2); return 0; }
int main() {
  pthread_t a;
  pthread_create(&a, 0, t1, 0);
  aa(4);
  pthread_join(a, 0);
  return 0;
}
