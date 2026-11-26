// Each worker fills in its own fresh node before any other thread can reach
// it, so the two init writes cannot race, and every list operation is under
// list_mutex.  Reduced from 28-race_reach_84-list2_racing2, keeping only what
// the defect needs: two lists chosen nondeterministically, and -- the part
// that matters -- main moving a node from one list to the other *after*
// spawning.  Under --refined-pointer-analysis the points-to sets are unioned
// until they stop growing, so main's `insert(p, B)` carries the workers'
// nodes and main looks like their publisher.  The filter must still exempt
// the init writes: what makes them safe is that they happen before the
// address is anywhere else, not who put it there.
//
// Without main's move the widening is not enough to mis-attribute anything
// and the test passes either way -- which is what a first version of it did.
#include <pthread.h>
#include <stdlib.h>
extern int __VERIFIER_nondet_int();
struct s
{
  int datum;
  struct s *next;
} * A, *B;
pthread_mutex_t list_mutex = PTHREAD_MUTEX_INITIALIZER;
void init(struct s *p)
{
  p->datum = 0;
  p->next = 0;
}
struct s *take(struct s *list)
{
  pthread_mutex_lock(&list_mutex);
  struct s *p = list;
  while(p->next != 0 && __VERIFIER_nondet_int())
    p = p->next;
  pthread_mutex_unlock(&list_mutex);
  return p;
}
void insert(struct s *node, struct s *list)
{
  pthread_mutex_lock(&list_mutex);
  struct s *t = list->next;
  list->next = node;
  node->next = t;
  pthread_mutex_unlock(&list_mutex);
}
void *worker(void *a)
{
  struct s *p = malloc(sizeof(struct s));
  if(p == 0)
    return 0;
  init(p);
  insert(p, __VERIFIER_nondet_int() ? A : B);
  return 0;
}
int main(void)
{
  pthread_t x, y;
  A = malloc(sizeof(struct s));
  B = malloc(sizeof(struct s));
  if(A == 0 || B == 0)
    return 0;
  init(A);
  init(B);
  pthread_create(&x, 0, worker, 0);
  pthread_create(&y, 0, worker, 0);
  struct s *p = take(A);
  insert(p, B);
  pthread_join(x, 0);
  pthread_join(y, 0);
  return 0;
}
