#include <pthread.h>
pthread_barrier_t barrier;
int main()
{
  int passed = 0;
  pthread_barrierattr_t attr;
  pthread_barrierattr_init(&attr);
  pthread_barrierattr_setpshared(&attr, PTHREAD_PROCESS_SHARED);
  pthread_barrier_init(&barrier, &attr, 2);
  pthread_barrier_wait(&barrier);
  passed = 1;
  __CPROVER_assert(passed == 0, "a process-shared barrier may be completed elsewhere");
  return 0;
}
