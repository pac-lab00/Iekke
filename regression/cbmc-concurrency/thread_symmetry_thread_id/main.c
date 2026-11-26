// A thread that reads its own identity can be told apart from its twin, so
// no ordering is added.

#include <assert.h>
#include <pthread.h>

extern __CPROVER_thread_local unsigned long __CPROVER_thread_id;

int x;

void *body(void *arg)
{
  (void)arg;
  if(__CPROVER_thread_id == 2)
    assert(x == 0);
  x = 1;
  return 0;
}

int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, body, 0);
  pthread_create(&b, 0, body, 0);
  return 0;
}
