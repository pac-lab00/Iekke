#include <assert.h>
#include <stdlib.h>

int nondet_int();

int main()
{
  int n = nondet_int();
  __CPROVER_assume(n >= 4 && n <= 8);
  // arrays of non-constant size
  int *a = malloc(n * sizeof(int));
  int *b = malloc(n * sizeof(int));
  for(int i = 0; i < 4; ++i)
  {
    a[i] = 0;
    b[i] = 0;
  }
  int k = nondet_int();
  __CPROVER_assume(k >= 0 && k <= 12);

  // byte updates at a non-constant offset
  char *c = (char *)a;
  c[k] = 1;
  c[k] = 2;
  short *s = (short *)((char *)b + k);
  *s = 0x0102;

  if(k == 5)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // the second update replaces the first one, the other bytes are unchanged
#ifdef TEST_BIG_ENDIAN
    assert(a[1] == 0x20000);
#else
    assert(a[1] == 0x200);
#endif
    // the update does not spill into the next element
    assert(a[2] == 0);
  }
  if(k == 7)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // a two-byte update across two elements
#ifdef TEST_BIG_ENDIAN
    assert(b[1] == 0x01 && b[2] == 0x02000000);
#else
    assert(b[1] == 0x02000000 && b[2] == 0x01);
#endif
  }

  return 0;
}
