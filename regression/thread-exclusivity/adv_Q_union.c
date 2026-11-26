// EXPECT: VERIFICATION FAILED under --rounds; u rejected with "2 roots".
// Exclusivity is tracked per base symbol, so different union members of the
// same object must not look like different variables.
//
// NEW ADVERSARIAL: two threads talk through different members of a union.
#include <pthread.h>
#include <assert.h>
union U { int a; unsigned b; } u;
void *t1(void *arg) { for(u.a = 0; u.a < 2; u.a++) {} assert(u.a == 2); return 0; }
void *t2(void *arg) { u.b = 99u; return 0; }
int main() {
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0); pthread_join(b, 0);
  return 0;
}
