// A zero-initialised global is array_of(0): every element is 0 until written.
int g[200];

int main()
{
  unsigned i, j;
  __CPROVER_assume(i < 200 && j < 200);
  __CPROVER_assert(g[i] == 0, "zero-initialised");
  g[j] = 3;
  if(i == j)
    __CPROVER_assert(g[i] == 3, "the written element");
  __CPROVER_assert(g[i] == 0, "the written element is not 0");
  return 0;
}
