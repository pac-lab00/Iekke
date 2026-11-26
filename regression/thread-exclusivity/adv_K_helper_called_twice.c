// ADVERSARIAL: a SINGLE pthread_create call site, not in a loop, but its
// enclosing helper is called twice by main -- so t1 still runs as two
// threads. Only the caller-chain part of the "runs at most once" check
// (spawn_one has two call sites) prevents a false "no bug found".
#include <pthread.h>
#include <assert.h>

int g = 0;

void *t1(void *arg)
{
  for(g = 0; g < 2; g++)
  {
  }
  assert(g == 2);
  return 0;
}

void spawn_one(pthread_t *id)
{
  pthread_create(id, 0, t1, 0);
}

int main()
{
  pthread_t a, b;
  spawn_one(&a);
  spawn_one(&b);
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
