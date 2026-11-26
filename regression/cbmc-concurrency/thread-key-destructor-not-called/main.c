// The destructor runs only for a thread that ends with a value set: not for
// main returning, and not for a worker that set nothing.
#include <assert.h>
#include <pthread.h>

void dtor(void *v)
{
  assert((long)v != 42);
}

void *worker(void *k)
{
  return 0;
}

int main(void)
{
  pthread_key_t key;
  pthread_key_create(&key, &dtor);
  pthread_t tid;
  pthread_create(&tid, 0, worker, &key);
  pthread_setspecific(key, (void *)42);
  pthread_join(tid, 0);
  return 0;
}
