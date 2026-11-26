#include <pthread.h>
#include <stdlib.h>
int nondet_int();

int *data;

void *t(void *arg)
{
  data[0] = (int)(long)arg + 1;
  __CPROVER_assert(data[0] == (int)(long)arg + 1, "shared slot");
  return 0;
}

int main(void)
{
  int n = nondet_int();
  __CPROVER_assume(n >= 2 && n <= 3);
  data = malloc(sizeof(int) * n);
  __CPROVER_assume(data != 0);
  data[0] = 0;
  data[1] = 0;
  pthread_t a, b;
  pthread_create(&a, 0, t, (void *)0);
  pthread_create(&b, 0, t, (void *)1);
  return 0;
}
