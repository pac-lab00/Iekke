// SOUNDNESS PROBE for the prologue fixpoint: the reused helper sits TWO
// levels below __CPROVER_initialize. myinit -> mid -> h. main calls mid()
// again AFTER spawning, so neither mid nor h may be in the prologue.
// Expect: VERIFICATION FAILED, g rejected with "2 roots", prologue must
// contain neither mid nor h.
#include <pthread.h>
#include <assert.h>
int g, other;
void h(int v) { g = v; }
void mid(int v) { h(v); }
__attribute__((constructor)) static void myinit(void) { mid(0); }
void *t1(void *a) { for(g = 0; g < 2; g++); assert(g == 2); return 0; }
void *t2(void *a) { other = 7; return 0; }
int main(void) {
  pthread_t x, y;
  pthread_create(&x, 0, t1, 0);
  pthread_create(&y, 0, t2, 0);
  mid(99);
  return 0;
}
