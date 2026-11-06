// Accesses through a pointer to _Atomic are accesses to the _Atomic object:
// no race, while the pointer itself is only read (pointer-to-atomic-racy is
// the race on the pointer).
#include <pthread.h>
_Atomic int v;
_Atomic int *p = &v;
void *thr(void *arg)
{
  *p = 1;
  return 0;
}
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  *p = 2;
  pthread_join(id, 0);
  return 0;
}
