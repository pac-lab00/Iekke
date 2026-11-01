#include <pthread.h>
pthread_barrier_t barrier;
int main()
{
  int passed = 0;
  pthread_barrierattr_t attr;
  pthread_barrierattr_init(&attr);
  pthread_barrierattr_setpshared(&attr, PTHREAD_PROCESS_PRIVATE);
  pthread_barrier_init(&barrier, &attr, 2);
  pthread_barrier_wait(&barrier);
  passed = 1;
  __CPROVER_assert(passed == 0, "a private barrier for two never completes with one thread");
  return 0;
}
