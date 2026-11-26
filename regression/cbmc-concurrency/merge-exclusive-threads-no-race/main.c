// Two creations of the same thread on paths that exclude each other, with
// different arguments. Main writes the object the thread does not write.
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
  int c = nondet_int();
  if(c)
    pthread_create(&t, 0, worker, &a);
  else
    pthread_create(&t, 0, worker, &b);
  if(c)
    b = 2;
  else
    a = 2;
  pthread_join(t, 0);
  return 0;
}
