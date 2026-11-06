// pthread_join hands back what the thread returned; the model never set
// *value_ptr (pthread-join-result/count-scale).
#include <pthread.h>
#include <assert.h>
int x;
void *worker(void *arg)
{
  return (void *)5;
}
int main(void)
{
  void *r = 0;
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  x = 1;
  pthread_join(t, &r);
  assert(r == (void *)5);
  return 0;
}
