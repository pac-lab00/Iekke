#include <pthread.h>
#include <stdlib.h>
int nondet_int();
struct s { int datum; struct s *next; };
pthread_mutex_t m[3];
struct s *slot[3];
void *t(void *a)
{
  int i = nondet_int();
  __CPROVER_assume(0 <= i && i < 3);
  pthread_mutex_lock(&m[i]);
  slot[i]->next = 0;
  pthread_mutex_unlock(&m[i]);
  return 0;
}
int main()
{
  for(int k = 0; k < 3; k++)
    slot[k] = malloc(sizeof(struct s));
  pthread_t h;
  pthread_create(&h, 0, t, 0);
  int j = nondet_int();
  __CPROVER_assume(0 <= j && j < 3);
  pthread_mutex_lock(&m[j]);
  struct s *p = slot[j]->next;
  pthread_mutex_unlock(&m[j]);
  return 0;
}
