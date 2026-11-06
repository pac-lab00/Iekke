// pthread_join hands back what the thread returned. A create immediately
// followed by its join is rewritten into a plain call, which dropped the
// result and left r as it was (pthread-join-result/lookup-wrong-key).
#include <pthread.h>
#include <assert.h>
void *worker(void *arg)
{
  return (void *)5;
}
int main(void)
{
  void *r = 0;
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, &r);
  assert(r == (void *)5);
  return 0;
}
