#include <pthread.h>
pthread_once_t once = PTHREAD_ONCE_INIT;
int ready;
void init(void) { ready = 1; }
void *f(void *p)
{
  pthread_once(&once, init);
  __CPROVER_assert(ready == 1, "the routine has run before pthread_once returns");
  return 0;
}
int main()
{
  pthread_t t;
  pthread_create(&t, 0, f, 0);
  pthread_once(&once, init);
  __CPROVER_assert(ready == 1, "the routine has run before pthread_once returns");
  pthread_join(t, 0);
  return 0;
}
