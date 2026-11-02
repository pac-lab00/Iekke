#include <pthread.h>
#include <stdint.h>
#include <assert.h>
int nondet_int();
struct node { uint64_t a; uint64_t b; };
struct lock { struct node n[3]; struct node *leaf[2]; } lk;
pthread_mutex_t m;
int which;
void *t1(void *x)
{
  int i = nondet_int();
  __CPROVER_assume(0 <= i && i < 2);
  which = i;
  struct node *p = lk.leaf[i];
  pthread_mutex_lock(&m);
  p->b = 1;
  pthread_mutex_unlock(&m);
  return 0;
}
void *t2(void *x)
{
  struct node *q = lk.leaf[1];
  pthread_mutex_lock(&m);
  q->a = 2;
  pthread_mutex_unlock(&m);
  return 0;
}
int main()
{
  lk.leaf[0] = &lk.n[0];
  lk.leaf[1] = &lk.n[2];
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);
  assert(lk.n[2].a == 2);
  assert(which != 1 || lk.n[2].b == 1);
#if 1
  assert(which != 1 || lk.n[2].b == 0);
#endif
  return 0;
}
