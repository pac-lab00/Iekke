// Race-free sibling of spawn_loop_racing: every access to x is under the same
// mutex, so no schedule of any number of threads violates the assertion. The
// verdict here is a *bounded* one -- "no violation with k threads created" --
// exactly as an --unwind verdict is "no violation within k iterations".
#include <pthread.h>

#define N 1000

int x;
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;

void *t_fun(void *arg)
{
  pthread_mutex_lock(&m);
  x++;
  x--;
  pthread_mutex_unlock(&m);
  return 0;
}

int main()
{
  pthread_t t_ids[N];
  for(int i = 0; i < N; i++)
    pthread_create(&t_ids[i], 0, t_fun, 0);

  pthread_mutex_lock(&m);
  __CPROVER_assert(x == 0, "x is only ever nonzero under the mutex");
  pthread_mutex_unlock(&m);

  for(int i = 0; i < N; i++)
    pthread_join(t_ids[i], 0);
  return 0;
}
