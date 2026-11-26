// A pointer to _Atomic is an ordinary object: writing p in two threads races,
// though what p points to is _Atomic (it was treated as atomic for the
// pointee's sake; pthread-atomic-qualifier/atomic-qual-ptr-to-atomic-write).
#include <pthread.h>
_Atomic int v1, v2;
_Atomic int *p;
void *thr(void *arg)
{
  p = &v1;
  return 0;
}
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  p = &v2;
  pthread_join(id, 0);
  return 0;
}
