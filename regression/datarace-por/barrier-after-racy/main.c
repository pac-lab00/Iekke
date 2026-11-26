#include <pthread.h>
pthread_barrier_t barrier;
int g;
void *f(void *p)
{
  pthread_barrier_wait(&barrier);
  g = 1;
  return 0;
}
int main()
{
  pthread_barrier_init(&barrier, 0, 2);
  pthread_t t;
  pthread_create(&t, 0, f, 0);
  pthread_barrier_wait(&barrier);
  g = 2;
  return 0;
}
