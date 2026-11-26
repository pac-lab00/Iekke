// Two creations on paths that exclude each other start different functions:
// the merged thread runs the one of the path that created it. Only the second
// one races with main.
#include <pthread.h>

int nondet_int(void);

int a, b;

void *write_a(void *p)
{
  a = 1;
  return 0;
}

void *write_b(void *p)
{
  b = 1;
  return 0;
}

int main(void)
{
  pthread_t t;
  int c = nondet_int();
  if(c)
    pthread_create(&t, 0, write_a, 0);
  else
    pthread_create(&t, 0, write_b, 0);
  b = 2;
  pthread_join(t, 0);
  return 0;
}
