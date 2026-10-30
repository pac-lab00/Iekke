// main is the only writer after the spawn; t can read either value, main
// reads its own
#include <assert.h>
#include <pthread.h>
int x;
int *p;
void *t(void *arg) { int v = x; return 0; }
int main(void)
{
  pthread_t a;
  p = &x;
  pthread_create(&a, 0, t, 0);
  *p = 3;
  assert(x == 3);
  return 0;
}
