#include <pthread.h>

// the thread may dereference x after f has returned
void *reader(void *arg)
{
  return (void *)(long)*(int *)arg;
}

pthread_t t;

void f(void)
{
  int x = 1;
  pthread_create(&t, 0, reader, &x);
}

int main(void)
{
  f();
  pthread_join(t, 0);
  return 0;
}
