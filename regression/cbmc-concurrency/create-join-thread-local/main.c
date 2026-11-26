// A thread created and joined at once still has its own copy of a
// thread-local variable: the worker's write does not reach main's copy.
#include <assert.h>
#include <pthread.h>

__thread int tls = 0;

void *worker(void *p)
{
  tls = 1;
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  assert(tls == 0);
  return 0;
}
