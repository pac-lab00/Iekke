#include <pthread.h>
#include <stdint.h>
int nondet_int();
struct node { uint64_t a; uint64_t b; };
struct lock { struct node n[3]; struct node *leaf[2]; } lk;
void *t1(void *x)
{
  int i = nondet_int();
  __CPROVER_assume(0 <= i && i < 2);
  /* the target node is one of two, loaded from the struct itself */
  struct node *p = lk.leaf[i];
  __atomic_store_n(&p->b, 1, __ATOMIC_SEQ_CST);
  return 0;
}
void *t2(void *x)
{
  /* a plain read of a pointer nobody writes after the spawn */
  struct node *q = lk.leaf[1];
  __atomic_store_n(&q->a, 2, __ATOMIC_SEQ_CST);
  return 0;
}
int main()
{
  lk.leaf[0] = &lk.n[0];
  lk.leaf[1] = &lk.n[2];
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  return 0;
}
