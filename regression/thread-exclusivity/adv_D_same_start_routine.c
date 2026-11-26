// ADVERSARIAL: g is mentioned ONLY inside t1, so a naive "appears in the
// reachable set of at most one thread entry" scan calls it thread-exclusive.
// But t1 is used as the start routine of TWO pthread_create calls, so TWO
// threads run it and both touch g. Only the "root spawned at most once" check
// stands between this program and a false "no bug found".
#include <pthread.h>
#include <assert.h>

int g = 0;

void *t1(void *arg)
{
  for(g = 0; g < 2; g++)
  {
  }
  assert(g == 2); // violable: the other instance of t1 can reset g
  return 0;
}

int main()
{
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t1, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
