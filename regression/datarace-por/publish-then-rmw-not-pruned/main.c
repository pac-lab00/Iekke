#include <pthread.h>
#include <stdlib.h>
#include <assert.h>
/* Under --datarace the thread must still be able to run past a
   post-publication read-modify-write of the node it published. The
   publication filter used to make that impossible (see
   publish-then-rmw-racy), so `done` was never set and the assertion was
   reported to hold. `other = 1` keeps the create and the join apart, which
   would otherwise be collapsed into a direct call. */
struct s { int datum; } *A;
int done, other;
void *t_fun(void *arg) {
  struct s *p = malloc(sizeof(struct s));
  p->datum = 7;
  A = p;
  p->datum++;
  done = 1;
  return 0;
}
int main(void) {
  pthread_t t;
  A = malloc(sizeof(struct s)); A->datum = 3;
  pthread_create(&t, 0, t_fun, 0);
  other = 1;
  pthread_join(t, 0);
  int v = A->datum;
  assert(!done);
  return 0;
}
