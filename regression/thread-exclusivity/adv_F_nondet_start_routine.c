// ADVERSARIAL: the start routine is not a literal function address, so the
// analysis must give up on the whole program.
#include <pthread.h>
#include <assert.h>

int g = 0;
int choice;

void *t1(void *arg)
{
  for(g = 0; g < 2; g++)
  {
  }
  assert(g == 2);
  return 0;
}

void *t2(void *arg)
{
  g = 99;
  return 0;
}

int main()
{
  pthread_t a, b;
  pthread_create(&a, 0, choice ? t1 : t2, 0);
  pthread_create(&b, 0, choice ? t2 : t1, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
