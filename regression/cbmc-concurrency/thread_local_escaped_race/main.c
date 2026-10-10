#include <pthread.h>
static __thread unsigned slot;
unsigned *volatile pub;
void *run(void *arg) {
  pub = &slot;
  slot = 1;
  return 0;
}
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, run, 0);
  unsigned *p = pub;
  if (p)
    *p = 2;
  pthread_join(t, 0);
  return 0;
}
