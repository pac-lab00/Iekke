#include <pthread.h>
#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
void assume_abort_if_not(int cond) { if(!cond) abort(); }
struct s { int datum; struct s *next; };
struct cache { struct s *slots[2]; pthread_mutex_t mutex[2]; } c;
void *t(void *arg)
{
  pthread_mutex_lock(&c.mutex[1]);
  c.slots[1]->next = 0;
  pthread_mutex_unlock(&c.mutex[1]);
  return 0;
}
int main(void)
{
  pthread_mutex_init(&c.mutex[0], 0);
  pthread_mutex_init(&c.mutex[1], 0);
  for(int k = 0; k < 2; k++)
    c.slots[k] = malloc(sizeof(struct s));
  int j = __VERIFIER_nondet_int();
  assume_abort_if_not(j == 0);
  pthread_t id;
  pthread_create(&id, 0, t, 0);
  pthread_mutex_lock(&c.mutex[j]);
  struct s *p = c.slots[j]->next;
  pthread_mutex_unlock(&c.mutex[j]);
  return 0;
}
