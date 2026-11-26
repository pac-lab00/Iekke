// Same as ia4 but main writes x: no race (the thread only writes y).
#include <pthread.h>
#include <stdlib.h>
struct s { int *first; int *second; };
void *my_alloc(unsigned long n) { void *r = malloc(n); __CPROVER_assume(r != 0); return r; }
int x, y;
struct s *g;
void *t(void *arg) { *g->second = 1; return 0; }
int main(void)
{
  void *tmp;
  tmp = my_alloc(12UL);
  g = (struct s *)tmp;
  g->first = &x;
  g->second = &y;
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  x = 2;
  pthread_join(id, 0);
  return 0;
}
