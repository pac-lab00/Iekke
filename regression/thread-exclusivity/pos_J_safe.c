// POSITIVE: p is thread-exclusive and the assertion about it holds. Must
// still report SUCCESSFUL.
#include <pthread.h>
#include <assert.h>

int p;
int i = 0;

void *t1(void *arg)
{
  for(p = 0; p < 3; p++)
    i++;
  assert(p == 3);
  return 0;
}

void *t2(void *arg)
{
  i = 7;
  return 0;
}

int main()
{
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
