#include <assert.h>
#include <stdlib.h>
#include <string.h>

int nondet_int();

int main()
{
  int n = nondet_int();
  __CPROVER_assume(n >= 4 && n <= 6);
  // an array of non-constant size and one of constant size, all bytes 0xff
  int *a = malloc(n * sizeof(int));
  int b[4];
  for(int i = 0; i < 4; ++i)
  {
    a[i] = -1;
    b[i] = -1;
  }
  char src[8] = {1, 2, 3, 4, 5, 6, 7, 8};
  int k = nondet_int();
  __CPROVER_assume(k >= 0 && k <= 4);
  int m = nondet_int();
  __CPROVER_assume(m >= 0 && m <= 8);

  // copies of non-constant length m, at the non-constant offset k into a and
  // at offset 0 into b
  memcpy((char *)a + k, src, m);
  memcpy(b, src, m);

  if(k == 1 && m == 2)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // within the first element
#ifdef TEST_BIG_ENDIAN
    assert(a[0] == 0xff0102ff);
#else
    assert(a[0] == 0xff0201ff);
#endif
    assert(a[1] == -1);
  }
  if(k == 0 && m == 8)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // ends at the end of an element
#ifdef TEST_BIG_ENDIAN
    assert(a[0] == 0x01020304 && a[1] == 0x05060708);
#else
    assert(a[0] == 0x04030201 && a[1] == 0x08070605);
#endif
    assert(a[2] == -1);
  }
  if(k == 2 && m == 4)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // across two elements
#ifdef TEST_BIG_ENDIAN
    assert(a[0] == 0xffff0102 && a[1] == 0x0304ffff);
#else
    assert(a[0] == 0x0201ffff && a[1] == 0xffff0403);
#endif
    assert(a[2] == -1);
  }
  if(k == 4 && m == 6)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // starts at the second element, ends within the third
#ifdef TEST_BIG_ENDIAN
    assert(a[1] == 0x01020304 && a[2] == 0x0506ffff);
#else
    assert(a[1] == 0x04030201 && a[2] == 0xffff0605);
#endif
    assert(a[0] == -1 && a[3] == -1);
  }
  if(k == 3 && m == 0)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // nothing is copied
    assert(a[0] == -1 && a[1] == -1);
  }
  if(m == 2)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
#ifdef TEST_BIG_ENDIAN
    assert(b[0] == 0x0102ffff);
#else
    assert(b[0] == 0xffff0201);
#endif
    assert(b[1] == -1);
  }
  if(m == 6)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
#ifdef TEST_BIG_ENDIAN
    assert(b[0] == 0x01020304 && b[1] == 0x0506ffff);
#else
    assert(b[0] == 0x04030201 && b[1] == 0xffff0605);
#endif
    assert(b[2] == -1);
  }
  if(m == 8)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
#ifdef TEST_BIG_ENDIAN
    assert(b[1] == 0x05060708);
#else
    assert(b[1] == 0x08070605);
#endif
    assert(b[2] == -1);
  }

  return 0;
}
