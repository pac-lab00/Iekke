// The merged thread is joined before main writes both objects: no race.
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
  pthread_join(t, 0);
  a = 2;
  b = 2;
  return 0;
}
