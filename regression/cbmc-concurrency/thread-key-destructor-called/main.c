// A thread-specific value with a destructor: the destructor runs when the
// worker ends, with the worker's value.
#include <assert.h>
#include <pthread.h>

void dtor(void *v)
{
  assert((long)v != 42);
}

void *worker(void *k)
{
  pthread_setspecific(*(pthread_key_t *)k, (void *)42);
  return 0;
}

int main(void)
{
  pthread_key_t key;
  pthread_key_create(&key, &dtor);
  pthread_t tid;
  pthread_create(&tid, 0, worker, &key);
  pthread_join(tid, 0);
  return 0;
}
