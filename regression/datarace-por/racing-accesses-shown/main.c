// The counterexample for a race must name both accesses that race, in two
// different threads. Shared accesses used to be dropped before the trace was
// built, so a race between a write here and a read in the other thread could
// produce a witness mentioning one thread only -- which cannot exhibit a race.
#include <pthread.h>

int glob;

void *reader(void *arg)
{
  int local = glob;
  (void)local;
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, reader, 0);
  glob = 1;
  pthread_join(t, 0);
  return 0;
}
