#include <pthread.h>
#include <stdlib.h>
int nondet_int();

int n;
int *data;
pthread_mutex_t *data_mutex;

void *t(void *arg)
{
  int i = (int)(long)arg;
  pthread_mutex_lock(&data_mutex[i]);
  data[i] = data[i] + 1;
  pthread_mutex_unlock(&data_mutex[i]);
  return 0;
}

int main(void)
{
  n = nondet_int();
  __CPROVER_assume(n >= 1 && n <= 2);
  data = calloc(n, sizeof(int));
  data_mutex = malloc(n * sizeof(pthread_mutex_t));
  __CPROVER_assume(data != 0 && data_mutex != 0);
  for(int i = 0; i < n; i++)
    pthread_mutex_init(&data_mutex[i], 0);
  pthread_t a, b;
  pthread_create(&a, 0, t, (void *)0);
  pthread_create(&b, 0, t, (void *)(long)(n - 1));
  return 0;
}
