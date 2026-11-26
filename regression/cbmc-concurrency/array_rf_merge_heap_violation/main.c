// array_rf_merge_heap with the writer able to run first: the reader can see
// 1 at a[1], so the assertion that it sees 5 fails.

#include <pthread.h>
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);

int *a;
int x, y;

void *safe_malloc(size_t size)
{
  void *p = malloc(size);
  if(!p)
    abort();
  return p;
}

int *fresh(int size)
{
  int *arr = (int *)safe_malloc(sizeof(int) * (size_t)size);
  for(int i = 0; i < size; i++)
    arr[i] = __VERIFIER_nondet_int();
  return arr;
}

void *writer(void *arg)
{
  (void)arg;
  a[1] = 1;
  return 0;
}

void *reader(void *arg)
{
  (void)arg;
  __VERIFIER_atomic_begin();
  x = a[1];
  y = a[0];
  __VERIFIER_atomic_end();
  return 0;
}

int main(void)
{
  int size = __VERIFIER_nondet_int();
  __CPROVER_assume(size >= 2 && size <= 3);
  a = fresh(size);
  if(__VERIFIER_nondet_int())
    a[0] = 7;
  else
    a[0] = 8;
  a[1] = 5;
  pthread_t w, r;
  pthread_create(&w, 0, writer, 0);
  pthread_create(&r, 0, reader, 0);
  pthread_join(w, 0);
  pthread_join(r, 0);
  __CPROVER_assert(x == 5, "the writer cannot run first -- false");
  return 0;
}
