// Two creations of the same thread on paths that exclude each other, with
// different arguments. Only the second one races with main.
#include <pthread.h>

int nondet_int(void);

int a, b;

void *worker(void *p)
{
  *(int *)p = 1;
  return 0;
}

int main(void)
{
  pthread_t t;
  if(nondet_int())
    pthread_create(&t, 0, worker, &a);
  else
    pthread_create(&t, 0, worker, &b);
  b = 2;
  pthread_join(t, 0);
  return 0;
}
