// main reads x and only then writes 5. Nothing else writes 5, so the read can
// never see it: a later write of the same thread is never before the read.

#include <pthread.h>

int x;

void *worker(void *arg)
{
  (void)arg;
  x = 3;
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  int r = x;
  x = 5;
  __CPROVER_assert(r != 5, "the read does not see main's later write");
  return 0;
}
