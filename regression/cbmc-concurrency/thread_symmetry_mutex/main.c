// Two identical threads increment x under a mutex; no update is lost. The
// threads stay interchangeable although the mutex records its owner.

#include <assert.h>
#include <pthread.h>

extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);

int x, done;
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;

void *inc(void *arg)
{
  (void)arg;
  pthread_mutex_lock(&m);
  int t = x;
  x = t + 1;
  pthread_mutex_unlock(&m);
  __VERIFIER_atomic_begin();
  int d = ++done;
  int v = x;
  __VERIFIER_atomic_end();
  if(d == 2)
    assert(v == 2);
  return 0;
}

int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, inc, 0);
  pthread_create(&b, 0, inc, 0);
  return 0;
}
