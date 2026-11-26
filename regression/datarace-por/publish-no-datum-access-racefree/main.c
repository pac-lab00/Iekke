#include <pthread.h>
#include <stdlib.h>
extern int __VERIFIER_nondet_int();
struct s { int datum; struct s *next; } *A;
pthread_mutex_t g = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t list_mutex = PTHREAD_MUTEX_INITIALIZER;
void init(struct s *p){ p->datum=0; p->next=0; }
struct s *take(struct s *list){ pthread_mutex_lock(&list_mutex); struct s *p=list;
  while (p->next != 0 && __VERIFIER_nondet_int()) p=p->next;
  pthread_mutex_unlock(&list_mutex); return p; }
void insert(struct s *node, struct s *list){ pthread_mutex_lock(&list_mutex);
  struct s *t=list->next; list->next=node; node->next=t; pthread_mutex_unlock(&list_mutex); }
void *t1(void *a){ struct s *p=malloc(sizeof(struct s)); insert(p,A); return 0; }
void *t2(void *a){ struct s *p=take(A); return 0; }
int main(void){ pthread_t x,y; A=malloc(sizeof(struct s)); init(A);
  pthread_create(&x,0,t1,0); pthread_create(&y,0,t2,0);
  pthread_join(x,0); pthread_join(y,0); return 0; }
