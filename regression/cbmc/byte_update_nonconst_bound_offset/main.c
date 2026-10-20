#include <assert.h>
#include <string.h>

int nondet_int();

struct S
{
  int a;
  int b;
};

int main()
{
  struct S s = {0x04030201, 0x08070605};
  char src[7] = {0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77};
  int m = nondet_int();
  __CPROVER_assume(m >= 0 && m <= 7);

  // a copy of non-constant length to offset 1 of a struct: the update of s.a
  // starts at byte 1, and only its first m bytes are written
  memcpy((char *)&s + 1, src, m);

  if(m == 1)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // byte 1 of s.a is written, bytes 2 and 3 are unchanged
#ifdef TEST_BIG_ENDIAN
    assert(s.a == 0x04110201);
#else
    assert(s.a == 0x04031101);
#endif
    assert(s.b == 0x08070605);
  }
  if(m == 5)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // bytes 1 to 3 of s.a and bytes 0 and 1 of s.b are written
#ifdef TEST_BIG_ENDIAN
    assert(s.a == 0x04112233 && s.b == 0x44550605);
#else
    assert(s.a == 0x33221101 && s.b == 0x08075544);
#endif
  }

  return 0;
}
