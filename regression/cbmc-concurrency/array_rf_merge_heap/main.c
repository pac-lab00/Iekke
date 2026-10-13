// A heap array in the shape of the weaver benchmarks: --array-rf has to take
// it, and still see what was written.
//
// Three things symex does here were each taken as a use of the array as a
// whole, which keeps the object on its chain -- on weaver/unroll-2 at u8 r7
// that was 97% of 10.5M clauses:
//  - where two paths of main join, after `if(!p) abort();`, the init loop and
//    the if/else below, it merges the array: `a#4 = c ? a#3 : a#2`;
//  - memory-leak tracking records the object as `(const void *)a`, its address;
//  - a read inside an atomic section copies the version read before indexing
//    it: `a#12 = a#11; x = a#12[1]`.
// A merge selects what the path that ran left behind, and the writes on that
// path are events guarded by its condition; the cast is an address; a copy is
// an unconditional equality. None of them observes the value.
//
// The reader sees 5 or the writer's 1 at a[1], and 7 or 8 at a[0]. Taking the
// merge as a havoc of the array would let it see anything at a[0].

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
  __CPROVER_assert(x == 5 || x == 1, "a[1] holds main's or the writer's value");
  __CPROVER_assert(y == 7 || y == 8, "a[0] holds one of main's values");
  return 0;
}
