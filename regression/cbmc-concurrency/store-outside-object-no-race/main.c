// A store whose bytes all lie outside the struct it is resolved against does
// not write the struct: no race with a read of one of its members.
#include <pthread.h>
struct s { int a; int b; } x;
void *t(void *arg)
{
  char *p = (char *)&x + 100;
  *(int *)p = 5;
  return 0;
}
int main(void)
{
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  int v = x.a;
  pthread_join(id, 0);
  return v;
}
