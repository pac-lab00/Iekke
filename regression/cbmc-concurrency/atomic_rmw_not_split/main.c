// C makes ++ and -- on an _Atomic lvalue a single atomic read-modify-write.
// If the load and the store are separately schedulable, two threads can
// interleave inside one increment and lose an update -- an execution the C
// abstract machine does not permit. Here that would make counter != 0
// reachable after both threads have finished, and the assertion would appear
// to fail on a program that cannot fail.
//
// The bug this guards against: _Atomic survives typechecking (c_qualifiers
// stores ID_C_atomic on the type) but was not acted on, so counter++ lowered
// to a bare ASSIGN with no atomic section. It needs >= 3 rounds to show, so
// --rounds 1 or 2 will pass either way; keep the bound in the flags below.
//
// Distilled from sv-benchmarks weaver/popl20-figure1.wvr.c, whose expected
// verdict is true.

#include <assert.h>
#include <pthread.h>

_Atomic int counter;

static void *inc(void *arg)
{
  (void)arg;
  for(int i = 0; i < 2; i++)
    counter++;
  return 0;
}

static void *dec(void *arg)
{
  (void)arg;
  for(int i = 0; i < 2; i++)
    counter--;
  return 0;
}

int main(void)
{
  pthread_t t1, t2;
  pthread_create(&t1, 0, inc, 0);
  pthread_create(&t2, 0, dec, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);

  // Two atomic increments and two atomic decrements, so this must hold.
  assert(counter == 0);
  return 0;
}
