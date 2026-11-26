// pthread.h declares pthread_self and pthread_key_create; a program that does
// not call them keeps the create/join collapse: the worker runs in thread 0.
#include <assert.h>
#include <pthread.h>

int x;

void *worker(void *arg)
{
  x = 1;
  assert(x == 2);
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  return 0;
}
