// POSITIVE. EXPECT: VERIFICATION FAILED under --rounds -- the assert(0) is
// genuinely reachable. g and h really are thread-exclusive here and folding
// them must not hide the real bug.
//
// NEW POSITIVE: g really is exclusive to t1, reached through a self-recursive
// helper. Folding must not hide the (real) bug.
#include <pthread.h>
#include <assert.h>
int g = 0;
int h = 0;
void rec(int n) { if(n > 0) { g++; rec(n - 1); } }
void *t1(void *arg) { rec(3); if(g == 3) assert(0); return 0; }
void *t2(void *arg) { h = 7; return 0; }
int main() {
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0); pthread_join(b, 0);
  return 0;
}
