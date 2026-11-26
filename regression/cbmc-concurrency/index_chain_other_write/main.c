// The other thread's write of 2 can come between main's write and main's read
// in some schedule of three rounds, so the assertion can fail.

#include <pthread.h>

int x;

void *worker(void *arg)
{
  (void)arg;
  x = 2;
  return 0;
}

int main(void)
{
  pthread_t t;
  x = 1;
  pthread_create(&t, 0, worker, 0);
  int r = x;
  __CPROVER_assert(r != 2, "the read never sees the other thread's write");
  return 0;
}
