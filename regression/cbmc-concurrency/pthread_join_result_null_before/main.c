// pthread_join writes *value_ptr and never reads it. The model dereferenced
// the old value as a pointer, so a result variable initialised to NULL was a
// NULL dereference (pthread-join-result/free-result, valid-memsafety).
#include <pthread.h>
#include <stdlib.h>
void *worker(void *arg)
{
  return malloc(4);
}
int main(void)
{
  void *r = 0;
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, &r);
  free(r);
  return 0;
}
