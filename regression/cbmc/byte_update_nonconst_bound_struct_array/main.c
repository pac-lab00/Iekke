#include <assert.h>
#include <string.h>

int nondet_int();

struct S
{
  int x[3];
};

int main()
{
  struct S s = {{0xa3a2a1a0, 0xb3b2b1b0, 0xc3c2c1c0}};
  char src[12] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
  int m = nondet_int();
  __CPROVER_assume(m >= 1 && m <= 11);

  // a copy of non-constant length into the array member of a struct: only the
  // first m bytes of the source are copied, the other bytes are unchanged
  memcpy(&s, src, m);

  if(m == 2)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
#ifdef TEST_BIG_ENDIAN
    assert(s.x[0] == 0x0102a1a0);
#else
    assert(s.x[0] == 0xa3a20201);
#endif
    assert(s.x[1] == 0xb3b2b1b0 && s.x[2] == 0xc3c2c1c0);
  }
  if(m == 6)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
#ifdef TEST_BIG_ENDIAN
    assert(s.x[0] == 0x01020304 && s.x[1] == 0x0506b1b0);
#else
    assert(s.x[0] == 0x04030201 && s.x[1] == 0xb3b20605);
#endif
    assert(s.x[2] == 0xc3c2c1c0);
  }
  if(m == 11)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
#ifdef TEST_BIG_ENDIAN
    assert(s.x[1] == 0x05060708 && s.x[2] == 0x090a0bc0);
#else
    assert(s.x[1] == 0x08070605 && s.x[2] == 0xc30b0a09);
#endif
  }

  return 0;
}
