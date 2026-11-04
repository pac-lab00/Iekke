// The witness says how far loops were unrolled (unroll-bound, read by
// Dartagnan, whose own witnesses carry it) and under which data model the
// task was checked (architecture: it said 32bit for every task).
#include <pthread.h>
int x;
void *t(void *arg)
{
  x = 1;
  return 0;
}
int main(void)
{
  pthread_t h;
  for(int i = 0; i < 2; i++)
    pthread_create(&h, 0, t, 0);
  x = 2;
  return 0;
}
