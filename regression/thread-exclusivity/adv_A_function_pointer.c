// ADVERSARIAL: t2 writes g only through a function pointer. A scan that did
// not follow the resolved indirect call (or bail out on it) would see g in
// t1 only and call it thread-exclusive.
#include <pthread.h>
#include <assert.h>

int g = 0;

void set99(void)
{
  g = 99;
}

void (*fp)(void) = set99;

void *t2(void *arg)
{
  fp();
  return 0;
}

void *t1(void *arg)
{
  for(g = 0; g < 2; g++)
  {
  }
  assert(g == 2); // violable: t2 calls set99 through fp
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
