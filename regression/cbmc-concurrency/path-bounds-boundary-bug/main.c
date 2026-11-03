#include <pthread.h>
#include <assert.h>
int __VERIFIER_nondet_int();
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
int slot[4];
pthread_mutex_t m[4];
void *t(void *x)
{
  int j = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= j);
  while(j < 4) {
    pthread_mutex_lock(&m[j]);
    slot[j]++;
    pthread_mutex_unlock(&m[j]);
    j++;
  }
  assert(j < 4 || j == 4);
  return 0;
}
int main()
{
  pthread_t h1, h2;
  pthread_create(&h1, 0, t, 0);
  pthread_create(&h2, 0, t, 0);
  pthread_join(h1, 0);
  pthread_join(h2, 0);
  return 0;
}
