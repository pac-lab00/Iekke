// A merged thread creates a thread of its own; the child sees the argument of
// the path that created its parent.
#include <assert.h>
#include <pthread.h>

int nondet_int(void);

int seen;

void *child(void *p)
{
  seen = *(int *)p;
  return 0;
}

void *parent(void *p)
{
  pthread_t c;
  pthread_create(&c, 0, child, p);
  pthread_join(c, 0);
  return 0;
}

int main(void)
{
  pthread_t t;
  int one = 1, two = 2;
  int c = nondet_int();
  if(c)
    pthread_create(&t, 0, parent, &one);
  else
    pthread_create(&t, 0, parent, &two);
  pthread_join(t, 0);
  assert(seen == (c ? 1 : 2));
  return 0;
}
