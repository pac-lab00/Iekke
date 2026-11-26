// The size of a heap object belongs to what the slicer must keep.
//
// data has a symbolic size, n * 4 bytes, and symex records it only in the type
// of the dynamic object, `int[n#k]`: the bounds check of data[c] reads it from
// there. thread_aware_slice collected the symbols of operands but not of
// types, so the assignment defining that size looked unused, was removed, and
// the size became whatever the solver liked: "pointer outside object bounds"
// on a store that c < n keeps in bounds. pthread-lit/sssc12 and sssc12_variant
// (valid-memsafety) were false alarms for the same reason.
//
// symbolic_size_slice_real is the same program with c <= n, which really
// writes past the end.

#include <pthread.h>
#include <stdlib.h>

extern unsigned __VERIFIER_nondet_uint(void);

int *data;
unsigned n;

void *thr(void *a)
{
  unsigned c = __VERIFIER_nondet_uint();
  if(c < n)
    data[c] = 1;
  return 0;
}

int main(void)
{
  pthread_t t, u;
  n = __VERIFIER_nondet_uint();
  if(n < 1 || n > 8)
    return 0;
  data = malloc(n * sizeof(int));
  if(!data)
    return 0;
  pthread_create(&t, 0, thr, 0);
  pthread_create(&u, 0, thr, 0);
  return 0;
}
