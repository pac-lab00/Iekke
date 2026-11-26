// ADVERSARIAL: g is syntactically mentioned only in t1 and in the static
// initializer of gp (which the prologue rule sets aside), so root counting
// alone would call g thread-exclusive. t2 writes g through gp without ever
// naming g. Only the dirtyt (address-taken) bailout prevents a false
// "no bug found".
#include <pthread.h>
#include <assert.h>

int g = 0;
int *gp = &g;

void *t2(void *arg)
{
  *gp = 99;
  return 0;
}

void *t1(void *arg)
{
  for(g = 0; g < 2; g++)
  {
  }
  assert(g == 2); // violable: t2 can store 99 into g
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
