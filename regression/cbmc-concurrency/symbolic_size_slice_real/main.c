// symbolic_size_slice with c <= n: the store at c == n is out of bounds, and
// keeping the size of data must not hide that.

#include <pthread.h>
#include <stdlib.h>

extern unsigned __VERIFIER_nondet_uint(void);

int *data;
unsigned n;

void *thr(void *a)
{
  unsigned c = __VERIFIER_nondet_uint();
  if(c <= n)
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
