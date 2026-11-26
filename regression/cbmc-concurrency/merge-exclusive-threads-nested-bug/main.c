// As merge-exclusive-threads-nested, with an assertion that fails on the
// path that passes 2: the merged thread does not lose that path.
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
  assert(seen == 1);
  return 0;
}
