// Mutual exclusion is carried entirely by the one byte of the mutex that
// CBMC's model touches -- __CPROVER_mutex_t is a signed char, written through
// a type-punned pointer, so the whole 192-bit pthread_mutex_t object becomes
// the shared object and its lazy chain is 24x wider than the state in it.
//
// This is the direction that catches a mistake in narrowing that chain: if the
// slice were taken at the wrong offset, or the chain lost the byte, the two
// threads could hold the lock at once, in_cs would reach 2, and a safe program
// would report a violation it does not have.

#include <pthread.h>

pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
int in_cs;

void *worker(void *arg)
{
  (void)arg;
  pthread_mutex_lock(&m);
  in_cs++;
  __CPROVER_assert(in_cs == 1, "at most one thread in the critical section");
  in_cs--;
  pthread_mutex_unlock(&m);
  return 0;
}

int main(void)
{
  pthread_t a, b;

  pthread_create(&a, 0, worker, 0);
  pthread_create(&b, 0, worker, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);

  return 0;
}
