// No symmetric family here, so the requested reduction cannot be applied.
//
// The two shared variables are not interchangeable: each thread names one of
// them directly, so there is no array family whose slots could be collapsed.
// The companion program in symmetric_instance_reduction is the positive case;
// this one exists to pin down what happens when the reduction is asked for and
// cannot be delivered.
//
// Falling back to the unreduced program would be the tempting behaviour, but
// it is not safe: --symmetric-instance is only ever passed together with an
// unwinding bound chosen for the *reduced* program. On the unreduced program
// that bound cuts the setup loop instead of completing it, the unwinding
// assumption prunes every path, and the run reports success having checked
// nothing. A vacuous safe answer on a task whose expected verdict is false is
// scored far worse than no answer at all, so cbmc must refuse instead.

#include <pthread.h>

int x;
int y;

void *thread_x(void *arg)
{
  (void)arg;
  x = x + 1;
  return 0;
}

void *thread_y(void *arg)
{
  (void)arg;
  y = y + 1;
  return 0;
}

int main(void)
{
  pthread_t a, b;

  pthread_create(&a, 0, thread_x, 0);
  pthread_create(&b, 0, thread_y, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);

  return 0;
}
