// The violation needs a value to travel between threads and back, so every
// round's read-from must be encoded for it to be found.
//
// x = 2 is reachable only along this hand-off:
//
//   thread a   writes x = 1
//   thread b   reads  x == 1, writes y = 1
//   thread a   reads  y == 1, writes x = 2
//
// which needs a to be scheduled, preempted, and scheduled again, i.e. a read
// taking its value from a write in a different round in each direction. Under
// --read-implication the per-round mux is replaced by one implication per
// round; if any round's implication were missing, the corresponding hand-off
// could not happen, the assumptions would be unsatisfiable, and the assertion
// would report SUCCESSFUL having proved nothing. So FAILED here is only
// reachable when the rewritten encoding is complete.

#include <pthread.h>

int x;
int y;

void *thread_a(void *arg)
{
  (void)arg;
  x = 1;
  __CPROVER_assume(y == 1);
  x = 2;
  return 0;
}

void *thread_b(void *arg)
{
  (void)arg;
  __CPROVER_assume(x == 1);
  y = 1;
  return 0;
}

int main(void)
{
  pthread_t a, b;

  pthread_create(&a, 0, thread_a, 0);
  pthread_create(&b, 0, thread_b, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);

  __CPROVER_assert(x != 2, "x never reaches 2");
  return 0;
}
