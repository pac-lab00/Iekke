// A local of a block nested in main is dead after the block, main still
// running: a thread that dereferences it then is invalid (valid-deref).
#include <pthread.h>
int *p;
void *worker(void *arg)
{
  return (void *)(long)*p;
}
int main(void)
{
  pthread_t t;
  {
    int inner = 1;
    p = &inner;
  }
  pthread_create(&t, 0, worker, 0);
  pthread_join(t, 0);
  return 0;
}
