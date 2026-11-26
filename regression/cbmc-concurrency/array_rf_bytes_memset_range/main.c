// A shared heap buffer of symbolic size, filled in two parts by memset with a
// symbolic length while another thread may already read it.
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
unsigned char *buf;
unsigned n;
int ready;
void *reader(void *arg)
{
  unsigned k = __VERIFIER_nondet_uint();
  __CPROVER_assume(k < n);
  __CPROVER_assume(ready);
  __CPROVER_assert(buf[k] == 97, "first part is 97");
  __CPROVER_assert(buf[n + k] == 98, "second part is 98");
  __CPROVER_assert(buf[k] == 98, "the first part is not 98");
  return 0;
}
int main()
{
  n = __VERIFIER_nondet_uint();
  __CPROVER_assume(n > 0 && n <= 4);
  buf = malloc(2 * n);
  __CPROVER_assume(buf != 0);
  pthread_t t;
  pthread_create(&t, 0, reader, 0);
  memset(buf, 97, n);
  memset(buf + n, 98, n);
  ready = 1;
  pthread_join(t, 0);
  return 0;
}
