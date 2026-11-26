#include <pthread.h>
#include <stdlib.h>
int nondet_int();
struct s { int datum; struct s *next; };
pthread_mutex_t m[2];
struct s *slot[2];
void *t(void *a)
{
  int i = nondet_int();
  __CPROVER_assume(0 <= i && i < 2);
  slot[i]->next = 0;
  return 0;
}
int main()
{
  for(int k = 0; k < 2; k++)
    slot[k] = malloc(sizeof(struct s));
  pthread_t h;
  pthread_create(&h, 0, t, 0);
  int j = nondet_int();
  __CPROVER_assume(0 <= j && j < 2);
  struct s *p = slot[j]->next;
  return 0;
}
