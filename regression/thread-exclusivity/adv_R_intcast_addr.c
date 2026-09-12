// EXPECT: VERIFICATION FAILED under --rounds; g must NOT appear in the
// exclusive set (the dirtyt address-taken check rejects it -- t2 never names
// g syntactically, so root counting alone would not save us).
//
// NEW ADVERSARIAL: t2 never names g; it reaches it through an integer-cast
// address stored in a global. Only dirtyt can save us.
#include <pthread.h>
#include <assert.h>
#include <stdint.h>
int g = 0;
uintptr_t ga = (uintptr_t)(void *)&g;
void *t1(void *arg) { for(g = 0; g < 2; g++) {} assert(g == 2); return 0; }
void *t2(void *arg) { *(int *)ga = 99; return 0; }
int main() {
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0); pthread_join(b, 0);
  return 0;
}
