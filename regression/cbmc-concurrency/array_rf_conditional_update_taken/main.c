// The thread writes through a pointer that may point into the heap array or
// at x. Symex turns `*p = 5` into the conditional point update
//   a#n = (POINTER_OBJECT(p) == POINTER_OBJECT(&a) ? a#k WITH [1 := 5] : a#k)
// which --array-rf takes as a write of 5 at index 1 that happens only where
// the condition holds. The array has a symbolic size, so --array-rf takes it
// whatever the cost model says.

#include <pthread.h>
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int *a;
int x;

void *t(void *arg)
{
  int *p = arg;
  *p = 5;
  return 0;
}

// a second thread running alongside, so that the program is concurrent: a
// create followed at once by its join is run as a plain call
void *u(void *arg)
{
  (void)arg;
  a[0] = 7;
  return 0;
}

int main(void)
{
  int n = __VERIFIER_nondet_int();
  __CPROVER_assume(n >= 2 && n <= 4);
  a = malloc(n * sizeof(int));
  a[1] = 0;
  int c = __VERIFIER_nondet_int();
  pthread_t id, id2;
  pthread_create(&id, 0, t, c ? &a[1] : &x);
  pthread_create(&id2, 0, u, 0);
  pthread_join(id, 0);
  pthread_join(id2, 0);
  __CPROVER_assert(!c || a[1] == 5, "a[1] is written whenever p points into a");
  return 0;
}
