// ADVERSARIAL: a single pthread_create call site, but inside a loop, so t1
// runs as several threads. Only the "call site not in a loop" part of the
// spawned-at-most-once check prevents a false "no bug found".
#include <pthread.h>
#include <assert.h>

int g = 0;

void *t1(void *arg)
{
  for(g = 0; g < 2; g++)
  {
  }
  assert(g == 2);
  return 0;
}

int main()
{
  pthread_t id[2];
  int k;
  for(k = 0; k < 2; k++)
    pthread_create(&id[k], 0, t1, 0);
  for(k = 0; k < 2; k++)
    pthread_join(id[k], 0);
  return 0;
}
