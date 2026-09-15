// ADVERSARIAL: the loop body does more than spawn a thread -- it also maintains
// a counter that later code reads. Bounding this loop would leave total == k
// and report a counterexample the program does not have. The analysis must
// refuse to classify it (a body instruction that is neither the pthread_create
// call nor the induction-variable update), leaving the ordinary
// assume(!guard) unwinding semantics in place.
#include <pthread.h>

#define N 1000

int total;

void *t_fun(void *arg)
{
  return 0;
}

int main()
{
  pthread_t t_ids[N];
  for(int i = 0; i < N; i++)
  {
    pthread_create(&t_ids[i], 0, t_fun, 0);
    total = total + 1;
  }

  __CPROVER_assert(total == N, "must NOT be reported: the loop really ran N times");
  return 0;
}
