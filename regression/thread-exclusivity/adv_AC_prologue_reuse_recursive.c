// PROBE: a RECURSIVE prologue helper. The least fixpoint must refuse to add
// rec (its second call site is inside itself, which is not yet prologue), so
// g gets counted for the initial thread as well -> not exclusive. This is a
// deliberate precision loss; it must not be a soundness loss.
// Expect: VERIFICATION FAILED, rec NOT in prologue.
#include <pthread.h>
#include <assert.h>
int g, other;
void rec(int n) { if(n > 0) { g = n; rec(n - 1); } }
__attribute__((constructor)) static void myinit(void) { rec(2); }
void *t1(void *a) { for(g = 0; g < 2; g++); assert(g == 2); return 0; }
void *t2(void *a) { other = 7; return 0; }
int main(void) {
  pthread_t x, y;
  pthread_create(&x, 0, t1, 0);
  pthread_create(&y, 0, t2, 0);
  rec(3);
  return 0;
}
