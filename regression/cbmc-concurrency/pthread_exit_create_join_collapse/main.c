#include <assert.h>
#include <pthread.h>
#include <stdlib.h>

// A thread created and immediately joined is collapsed into a plain call,
// which is sound for the schedule -- nothing can interleave between the two --
// but not when the body ends in pthread_exit. That model ends in
// __CPROVER_assume(0), meaning "this thread stops here"; once the body runs as
// an ordinary call the state holds a single thread, the assumption goes into
// the global formula, and it comes to mean "this execution is infeasible".
//
// Before the fix the whole tail of the program was dropped before reaching the
// equation: both assertions below disappeared, and so did the memory-leak
// check that always sits at the end of __CPROVER__start. The program was
// reported SUCCESSFUL having checked nothing at all.

int x = 0;

void *writer(void *arg)
{
  x = 1;
  pthread_exit(0);
}

void *leaker(void *arg)
{
  int *p = malloc(sizeof(int));
  *p = 1;
  pthread_exit(0); // the allocation is unreachable from here on: a leak
}

int main(void)
{
  pthread_t t1, t2;

  // Create/join pairs, so both are candidates for the collapse.
  pthread_create(&t1, 0, writer, 0);
  pthread_join(t1, 0);
  pthread_create(&t2, 0, leaker, 0);
  pthread_join(t2, 0);

  // Reachable and violated. Dropped entirely before the fix.
  assert(x == 0);

  return 0;
}
