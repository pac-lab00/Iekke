// The ldv-linux nsc-ircc pattern with threads: netdev_priv is dev + 3200,
// whole structs past the block, and a thread reads the private state through
// it. The load is wholly outside the shared struct: its value is
// unconstrained, and none of the struct's bits are needed for it.
#include <assert.h>
#include <pthread.h>
#include <stdlib.h>
struct big { int a[64]; };
struct priv { int x; int y; };
struct big *dev;
int out;
void *t(void *arg)
{
  struct priv *self = (struct priv *)(dev + 3);
  out = self->y;
  assert(out != 12345); // must fail: the value is unconstrained
  return 0;
}
int main(void)
{
  dev = malloc(sizeof(struct big));
  __CPROVER_assume(dev != 0);
  dev->a[0] = 1;
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  pthread_join(id, 0);
  return out;
}
