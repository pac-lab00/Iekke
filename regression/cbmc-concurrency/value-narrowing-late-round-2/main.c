#include <pthread.h>
int x, y;
void *t1(void *a)
{
  for(int i = 0; i < 3; i++)
    x = y + 1;
  return 0;
}
void *t2(void *a)
{
  for(int i = 0; i < 3; i++)
    y = x + 1;
  __CPROVER_assert(y != 6, "y needs three rounds to reach 6");
  return 0;
}
int main()
{
  pthread_t h1, h2;
  pthread_create(&h1, 0, t1, 0);
  pthread_create(&h2, 0, t2, 0);
  return 0;
}
