// The same framing problem without any array: "if(c) x = 1;" is lowered to
// x = c ? 1 : x, and the else branch frames x over from a read taken before
// the write. Published as an unconditional shared write that resets whatever
// the other thread stored in between, even though c is always 0 here and T1
// never writes x at all.
#include <pthread.h>

int x, c;

void *T1(void *p)
{
  if(c)
    x = 1;
  return 0;
}
void *T2(void *p)
{
  x = 2;
  return 0;
}

int main()
{
  c = 0;
  pthread_t t1, t2;
  pthread_create(&t1, 0, T1, 0);
  pthread_create(&t2, 0, T2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  __CPROVER_assert(x == 2, "a write the program never performs cannot clobber");
  return 0;
}
