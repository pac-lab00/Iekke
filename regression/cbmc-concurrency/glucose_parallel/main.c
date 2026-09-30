// The portfolio backend must reach the same verdict as the sequential one.
//
// A portfolio solver is nondeterministic in which thread finds the answer and
// in the model it returns, but satisfiability is not, so the verdict is a
// sound thing to assert even though the search is not reproducible.
//
// The violation here needs a value to cross between threads, so it exercises
// the read-from encoding rather than being decided by propagation alone: a
// backend that dropped clauses on the way to MultiSolvers would report
// SUCCESSFUL here.

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
