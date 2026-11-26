// ADVERSARIAL: t1 is a start routine AND is also called directly by main, so
// two threads execute its body. Root counting must see both.
#include <pthread.h>
#include <assert.h>

int g = 0;

void *t1(void *arg)
{
  for(g = 0; g < 2; g++)
  {
  }
  assert(g == 2);
  return 0;
}

int main()
{
  pthread_t a;
  pthread_create(&a, 0, t1, 0);
  t1(0); // main runs the same body concurrently with the spawned thread
  pthread_join(a, 0);
  return 0;
}
