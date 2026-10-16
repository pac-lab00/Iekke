// Both threads joined before the check: the ordering applies, and the answer
// is unchanged.

#include <assert.h>
#include <pthread.h>

int done;

void *body(void *arg)
{
  (void)arg;
  __CPROVER_atomic_begin();
  done++;
  __CPROVER_atomic_end();
  return 0;
}

int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, body, 0);
  pthread_create(&b, 0, body, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  assert(done == 2);
  return 0;
}
