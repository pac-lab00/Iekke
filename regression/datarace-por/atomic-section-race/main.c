// A race where one side sits inside an atomic section. The trace builder
// marks an open atomic section by negating its clock and restores it when the
// section ends; a violation reported while that marker was still outstanding
// used to sort ahead of every event and truncate the counterexample to
// nothing. The race here is real: the atomic section makes the increment
// indivisible but does not synchronise with the other thread.
#include <pthread.h>

extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);

int shared;

void *worker(void *arg)
{
  __VERIFIER_atomic_begin();
  shared = shared + 1;
  __VERIFIER_atomic_end();
  return 0;
}

int main(void)
{
  pthread_t t;
  pthread_create(&t, 0, worker, 0);
  shared = 2;
  pthread_join(t, 0);
  return 0;
}
