// main reads x after writing it itself; the other thread writes 2. The read
// sees main's own write (1) or the other thread's (2), never the initial 0:
// main's write comes first in its program order, so it is always in the chain
// before the read.

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
  __CPROVER_assert(r == 1 || r == 2, "the read sees one of the two writes");
  return 0;
}
