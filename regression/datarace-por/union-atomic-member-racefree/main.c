// Both threads access the union only through its _Atomic member: no race.
// A union is one object to the race encoding, so the member write looked
// like a plain write of the whole union
// (pthread-atomic-qualifier/atomic-qual-union-member was answered FALSE).
#include <pthread.h>
union U { _Atomic int f; long g; };
union U u;
int r;
void *thr(void *arg)
{
  u.f = 1;
  return 0;
}
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  u.f = 2;
  r = u.f;
  pthread_join(id, 0);
  return 0;
}
