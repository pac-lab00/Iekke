// The plain member is written through a pointer, so the instruction does not
// name the union: a race with the _Atomic member write.
#include <pthread.h>
union U { _Atomic int f; long g; };
union U u;
long *p = &u.g;
void *thr(void *arg)
{
  *p = 1;
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
