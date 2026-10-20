#include <assert.h>
#include <stdlib.h>
#include <string.h>

int nondet_int();

// 6 bytes: x at 0, y at 1, z at 2, w at 4
struct S
{
  unsigned char x;
  unsigned char y;
  unsigned short z;
  unsigned short w;
};

int main()
{
  int n = nondet_int();
  __CPROVER_assume(n >= 8 && n <= 10);
  // arrays of non-constant size
  int *a = malloc(n * sizeof(int));
  int *b = malloc(n * sizeof(int));
  for(int i = 0; i < 8; ++i)
  {
    a[i] = 0;
    b[i] = 0;
  }

  unsigned char src[12];
  for(int i = 0; i < 12; ++i)
    src[i] = 0x11 + i;
  struct S s = {0x21, 0x22, 0x2423, 0x2625};

  int k = nondet_int();
  __CPROVER_assume(k >= 0 && k <= 16);

  // a 12-byte update spanning four or five elements, at a non-constant offset
  memcpy((char *)a + k, src, 12);
  // a 6-byte struct update spanning two or three elements
  *(struct S *)((char *)b + k) = s;

  if(k == 5)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // bytes 5..16 of a are 0x11..0x1c
#ifdef TEST_BIG_ENDIAN
    assert(a[0] == 0 && a[1] == 0x00111213 && a[2] == 0x14151617);
    assert(a[3] == 0x18191a1b && a[4] == 0x1c000000 && a[5] == 0);
#else
    assert(a[0] == 0 && a[1] == 0x13121100 && a[2] == 0x17161514);
    assert(a[3] == 0x1b1a1918 && a[4] == 0x1c && a[5] == 0);
#endif
  }
  if(k == 3)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // bytes 3..14 of a are 0x11..0x1c: one byte in the first element
#ifdef TEST_BIG_ENDIAN
    assert(a[0] == 0x11 && a[1] == 0x12131415 && a[2] == 0x16171819);
    assert(a[3] == 0x1a1b1c00 && a[4] == 0);
#else
    assert(a[0] == 0x11000000 && a[1] == 0x15141312 && a[2] == 0x19181716);
    assert(a[3] == 0x001c1b1a && a[4] == 0);
#endif
    // bytes 3..8 of b are the bytes of s
#ifdef TEST_BIG_ENDIAN
    // 0x21 0x22 0x24 0x23 0x26 0x25
    assert(b[0] == 0x21 && b[1] == 0x22242326 && b[2] == 0x25000000);
#else
    // 0x21 0x22 0x23 0x24 0x25 0x26
    assert(b[0] == 0x21000000 && b[1] == 0x25242322 && b[2] == 0x26);
#endif
    assert(b[3] == 0);
  }
  if(k == 2)
  {
#ifdef CHECK_REACHABLE
    assert(0); // this branch is reached
#endif
    // bytes 2..7 of b are the bytes of s
#ifdef TEST_BIG_ENDIAN
    assert(b[0] == 0x2122 && b[1] == 0x24232625 && b[2] == 0);
#else
    assert(b[0] == 0x22210000 && b[1] == 0x26252423 && b[2] == 0);
#endif
  }

  return 0;
}
