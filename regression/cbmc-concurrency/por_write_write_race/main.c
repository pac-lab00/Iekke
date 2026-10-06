#include <pthread.h>

// POR must not prune a schedule that exhibits a data race.
//
// `datum` is written under a mutex by the spawned thread and without any
// mutex by main, so the two writes race. Nothing ever reads `datum`, so the
// two orders of those writes are read-from equivalent: whichever runs last,
// no read can tell. That is exactly the equivalence POR's canonicality
// quotients the schedules by, and for reachability it is sound -- the two
// executions compute the same thing. A data race is not a property of what is
// computed, though, but of which accesses are concurrent, and it is not
// preserved by that equivalence.
//
// The reduction therefore used to drop the racing schedule and answer
// SUCCESSFUL here, while --no-por answered FAILED on the same program.

int datum;
pthread_mutex_t datum_mutex = PTHREAD_MUTEX_INITIALIZER;

void *thread(void *arg)
{
  pthread_mutex_lock(&datum_mutex);
  datum = 5;
  pthread_mutex_unlock(&datum_mutex);
  return 0;
}

int main(void)
{
  pthread_t id;

  pthread_create(&id, 0, &thread, 0);
  datum = 8; // unprotected: races with the write inside the critical section

  return 0;
}
