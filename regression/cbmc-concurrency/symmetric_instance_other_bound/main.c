#include <assert.h>
#include <pthread.h>

int a[6];

void *worker(void *arg)
{
  (void)arg;
  for(int i = 0; i < 3; i++)
    assert(a[i] == 0);
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  return 0;
}
