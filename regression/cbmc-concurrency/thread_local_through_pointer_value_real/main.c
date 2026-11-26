#include <pthread.h>
#include <assert.h>
static __thread unsigned slot = 7;
void bump(unsigned *s) { *s = *s + 1; }
void *run(void *arg) {
  bump(&slot);
  assert(slot == 9);
  return 0;
}
int main(void) {
  pthread_t t[2];
  for (int i = 0; i < 2; i++) pthread_create(&t[i], 0, run, 0);
  for (int i = 0; i < 2; i++) pthread_join(t[i], 0);
  return 0;
}
