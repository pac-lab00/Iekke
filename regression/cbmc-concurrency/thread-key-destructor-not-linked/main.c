// A program that creates no thread-specific key: the destructor code is not
// linked, so the call at thread end has no body. Linked into every program,
// it made each thread end dispatch a function pointer over all compatible
// functions, the thread routine among them.
#include <assert.h>
#include <pthread.h>

int x;

void *worker(void *arg)
{
  x = 1;
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  return 0;
}
