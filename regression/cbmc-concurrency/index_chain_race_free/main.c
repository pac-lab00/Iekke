// The same two writes under one mutex: no data race, at seven rounds with
// partial-order reduction, the configuration the wrapper uses there.

#include <pthread.h>

pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
int x;

void *worker(void *arg)
{
  (void)arg;
  pthread_mutex_lock(&m);
  x = x + 1;
  pthread_mutex_unlock(&m);
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_mutex_lock(&m);
  x = x + 2;
  pthread_mutex_unlock(&m);
  pthread_join(t, 0);
  return x;
}
