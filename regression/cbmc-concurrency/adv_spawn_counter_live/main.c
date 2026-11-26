// ADVERSARIAL: the induction variable outlives the loop, so later code can see
// that the loop stopped early. The analysis must refuse to classify the loop
// (its counter is not DEAD at the loop exit).
#include <pthread.h>

#define N 1000

void *t_fun(void *arg)
{
  return 0;
}

int main()
{
  pthread_t t_ids[N];
  int i;
  for(i = 0; i < N; i++)
    pthread_create(&t_ids[i], 0, t_fun, 0);

  __CPROVER_assert(i == N, "must NOT be reported: the loop really ran N times");
  return 0;
}
