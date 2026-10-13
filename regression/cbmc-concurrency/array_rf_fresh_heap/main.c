// a[0] of freshly allocated memory is never written, so its value is whatever
// malloc returned. --array-rf takes the allocation, a whole-array write of a
// nondeterministic array, as the value every element holds until written:
// element j holds that array's j-th entry, not a constant.

#include <pthread.h>
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int *a;

void *t(void *arg)
{
  (void)arg;
  a[1] = 1;
  return 0;
}

// a second thread running alongside, so that the program is concurrent: a
// create followed at once by its join is run as a plain call
void *u(void *arg)
{
  (void)arg;
  a[1] = 2;
  return 0;
}

int main(void)
{
  int n = __VERIFIER_nondet_int();
  __CPROVER_assume(n >= 2 && n <= 4);
  a = malloc(n * sizeof(int));
  pthread_t id, id2;
  pthread_create(&id, 0, t, 0);
  pthread_create(&id2, 0, u, 0);
  pthread_join(id, 0);
  pthread_join(id2, 0);
  __CPROVER_assert(a[0] == 0, "fresh heap memory is zero -- false");
  return 0;
}
