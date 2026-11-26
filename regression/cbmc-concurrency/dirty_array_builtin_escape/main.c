// A local array passed to an array builtin AND to a thread: the thread's
// access goes through a pointer, so the array is dirty and the two accesses
// race. The builtin's own operand does not make it dirty; the thread
// argument does.
#include <pthread.h>
void *t(void *arg)
{
  ((int *)arg)[0] = 1;
  return 0;
}
int main()
{
  int a[4];
  pthread_t id;
  pthread_create(&id, 0, t, a);
  __CPROVER_array_set(a, 0);
  pthread_join(id, 0);
  return 0;
}
