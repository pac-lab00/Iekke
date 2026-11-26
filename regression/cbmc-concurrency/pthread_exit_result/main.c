// The value passed to pthread_exit is what pthread_join hands back.
#include <pthread.h>
#include <assert.h>
void *worker(void *arg)
{
  pthread_exit((void *)7);
  return 0;
}
int main(void)
{
  void *r = 0;
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, &r);
  assert(r == (void *)7);
  return 0;
}
