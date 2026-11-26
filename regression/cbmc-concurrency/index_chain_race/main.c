// Two threads write x with no lock between them: a data race, which
// --index-chain must leave as visible as the value chain does.

#include <pthread.h>

int x;

void *worker(void *arg)
{
  (void)arg;
  x = 1;
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  x = 2;
  pthread_join(t, 0);
  return x;
}
