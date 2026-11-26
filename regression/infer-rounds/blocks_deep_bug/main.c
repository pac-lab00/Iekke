int i = 1, j = 1;

void t1(void)
{
  for(int k = 0; k < 5; k++)
  {
    __CPROVER_atomic_begin();
    i = i + j;
    __CPROVER_atomic_end();
  }
}

void t2(void)
{
  for(int k = 0; k < 5; k++)
  {
    __CPROVER_atomic_begin();
    j = j + i;
    __CPROVER_atomic_end();
  }
}

int main(void)
{
  __CPROVER_ASYNC_1: t1();
  __CPROVER_ASYNC_2: t2();
  __CPROVER_atomic_begin();
  int ok = i < 144 && j < 144;
  __CPROVER_atomic_end();
  __CPROVER_assert(ok, "fib(12) is reached only by full alternation");
  return 0;
}
