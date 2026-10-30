// prologue writes x on one path before a spawn on that path; read by a thread
// spawned on both paths: must see 1 on the other path
#include <assert.h>
#include <pthread.h>
int x = 1;
int nondet_int(void);
void *idle(void *arg) { return 0; }
void *t(void *arg) { assert(x == 2); return 0; }
int main(void)
{
  pthread_t a, b;
  if(nondet_int())
  {
    x = 2;
    pthread_create(&a, 0, idle, 0);
  }
  pthread_create(&b, 0, t, 0);
  return 0;
}
