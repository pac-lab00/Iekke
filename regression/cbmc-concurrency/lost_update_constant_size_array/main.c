// A 65-byte array (too large to split, small enough to bit-blast), filled in
// halves by two threads in loops: many accesses, so the access-based encoding
// is declined by its cost model and stores rebuild the whole array.
#include <pthread.h>
char a[65];
void *t1(void *arg) { for(int i = 0; i < 8; i++) a[i] = 1; return 0; }
void *t2(void *arg) { for(int i = 0; i < 8; i++) a[32 + i] = 2; return 0; }
int main()
{
  pthread_t x, y;
  pthread_create(&x, 0, t1, 0);
  pthread_create(&y, 0, t2, 0);
  pthread_join(x, 0);
  pthread_join(y, 0);
  __CPROVER_assert(a[0] == 1 && a[32] == 2, "both halves survive");
  return 0;
}
