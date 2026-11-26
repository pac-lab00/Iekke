// Two creations of the same thread on paths that exclude each other: the
// thread sees the argument of the path that created it.
#include <assert.h>
#include <pthread.h>

int nondet_int(void);

int result;

void *worker(void *p)
{
  result = *(int *)p;
  return 0;
}

int main(void)
{
  pthread_t t;
  int one = 1, two = 2;
  int c = nondet_int();
  if(c)
    pthread_create(&t, 0, worker, &one);
  else
    pthread_create(&t, 0, worker, &two);
  pthread_join(t, 0);
  assert(result == (c ? 1 : 2));
  assert(result == 1);
  return 0;
}
