// A load whose bytes all lie outside the struct it is resolved against does
// not read the struct: no race with a write of one of its members.
#include <pthread.h>
struct s { int a; int b; } x;
int out;
void *t(void *arg)
{
  out = *(int *)((char *)&x + 100);
  return 0;
}
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  x.a = 1;
  pthread_join(id, 0);
  return 0;
}
