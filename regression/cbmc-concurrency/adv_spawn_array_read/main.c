// ADVERSARIAL: the thread-handle array is read outside the spawn/join loops, so
// later code can see that only the first k entries were written. The analysis
// must refuse to classify the loop (the array is mentioned outside it).
#include <pthread.h>

#define N 1000

void *t_fun(void *arg)
{
  return 0;
}

int main()
{
  pthread_t t_ids[N];
  for(int i = 0; i < N; i++)
    pthread_create(&t_ids[i], 0, t_fun, 0);

  __CPROVER_assert(
    t_ids[N - 1] != 0, "must NOT be reported: that handle really was written");
  return 0;
}
