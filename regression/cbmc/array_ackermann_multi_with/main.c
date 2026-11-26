// An int stored into a char array at a symbolic offset is an update of four
// elements at once; a read at an index equal to one of them sees that byte.
int main()
{
  unsigned char buf[400];
  unsigned off, i, j;
  __CPROVER_assume(off < 396 && i < 400 && j < 400);
  *(unsigned *)(buf + off) = 0x04030201u;
  if(i == off + 1)
    __CPROVER_assert(buf[i] == 2, "second byte, little endian");
  if(i == j)
    __CPROVER_assert(buf[i] == buf[j], "equal indices, equal elements");
  __CPROVER_assert(buf[i] == 2, "other bytes are unconstrained");
  return 0;
}
