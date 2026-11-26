// array_rf_prologue_fold with the writer able to run first: the reader can
// see 9 at a[1].

#include <pthread.h>
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int *a;
int c, x, y;

void *writer(void *arg)
{
  (void)arg;
  a[1] = 9;
  return 0;
}

void *reader(void *arg)
{
  (void)arg;
  x = a[1];
  y = a[0];
  return 0;
}

int main(void)
{
  int size = __VERIFIER_nondet_int();
  __CPROVER_assume(size >= 2 && size <= 3);
  a = malloc(size * sizeof(int));
  if(!a)
    abort();
  for(int i = 0; i < size; i++)
    a[i] = 0;
  c = __VERIFIER_nondet_int();
  if(c)
    a[0] = 7;
  a[1] = 3;
  a[1] = 4;
  pthread_t w, r;
  pthread_create(&w, 0, writer, 0);
  pthread_create(&r, 0, reader, 0);
  pthread_join(w, 0);
  pthread_join(r, 0);
  __CPROVER_assert(x == 4, "the writer cannot run before the reader -- false");
  return 0;
}
