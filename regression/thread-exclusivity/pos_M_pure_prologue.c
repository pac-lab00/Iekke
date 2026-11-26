// PRECISION PROBE: h is reached ONLY through the prologue chain
// __CPROVER_initialize -> myinit -> h. Nothing calls it post-spawn, so the
// fixpoint must still admit myinit AND h, and g must still be exclusive to
// t1 (otherwise the fix has over-tightened and the analysis stops firing).
// Expect: VERIFICATION FAILED (the assert(g==3) is genuinely violated
// because the loop runs to 2), prologue must contain myinit and h.
#include <pthread.h>
#include <assert.h>
int g, other;
void h(int v) { g = v; }
__attribute__((constructor)) static void myinit(void) { h(0); }
void *t1(void *a) { for(g = 0; g < 2; g++); assert(g == 3); return 0; }
void *t2(void *a) { other = 7; return 0; }
int main(void) {
  pthread_t x, y;
  pthread_create(&x, 0, t1, 0);
  pthread_create(&y, 0, t2, 0);
  return 0;
}
