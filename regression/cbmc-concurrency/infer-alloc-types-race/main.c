// Race through a heap block allocated by a wrapper with an oversized constant
// and typed by the cast after the call: the race must still be found.
#include <pthread.h>
#include <stdlib.h>
struct s { int a; int *p; int b; };
void *my_alloc(unsigned long n) { void *r = malloc(n); __CPROVER_assume(r != 0); return r; }
struct s *g;
void *t(void *arg) { g->b = 1; return 0; }
int main(void)
{
  void *tmp;
  tmp = my_alloc(20UL);
  g = (struct s *)tmp;
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  g->b = 2;
  pthread_join(id, 0);
  return 0;
}
