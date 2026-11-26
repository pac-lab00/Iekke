// The other thread writes the plain member of the same union: a race,
// though one of the two accesses is _Atomic.
#include <pthread.h>
union U { _Atomic int f; long g; };
union U u;
void *thr(void *arg)
{
  u.g = 1;
  return 0;
}
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  u.f = 2;
  pthread_join(id, 0);
  return 0;
}
