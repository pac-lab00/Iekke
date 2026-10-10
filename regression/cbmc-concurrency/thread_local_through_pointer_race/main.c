#include <pthread.h>
static unsigned slot;
void set(unsigned *s, unsigned v) { *s = v; }
void *run(void *arg) {
  set(&slot, (unsigned)(unsigned long)arg);
  return 0;
}
int main(void) {
  pthread_t t[2];
  for (unsigned long i = 0; i < 2; i++)
    pthread_create(&t[i], 0, run, (void *)i);
  for (int i = 0; i < 2; i++)
    pthread_join(t[i], 0);
  return 0;
}
