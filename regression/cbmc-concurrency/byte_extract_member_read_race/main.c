#include <pthread.h>
int __VERIFIER_nondet_int(void);
typedef struct C { struct C *n; int d; } C;
typedef struct T { unsigned id; int op; C cell; } T;
T th[4];
C *top;
void *reader(void *a) {
  C *ph = top;
  if (ph != 0) { C *nx = ph->n; (void)nx; }
  return 0;
}
int main(void) {
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= i && i < 4);
  top = &th[i].cell;
  pthread_t t;
  pthread_create(&t, 0, reader, 0);
  th[0].cell.n = 0;
  pthread_join(t, 0);
  return 0;
}
