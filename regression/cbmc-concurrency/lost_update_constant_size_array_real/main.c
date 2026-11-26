// Both threads increment the same element of a 65-byte array without a lock:
// a real lost update, which must still be found.
#include <pthread.h>
char a[65];
void *t(void *arg) { for(int i = 0; i < 8; i++) a[i] = a[i] + 1; a[40] = a[40] + 1; return 0; }
int main()
{
  pthread_t x, y;
  pthread_create(&x, 0, t, 0);
  pthread_create(&y, 0, t, 0);
  pthread_join(x, 0);
  pthread_join(y, 0);
  __CPROVER_assert(a[40] == 2, "no increment lost");
  return 0;
}
