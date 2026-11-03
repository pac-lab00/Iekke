int i = 1, j = 1, x = 0;

void t1(void)
{
  for(int k = 0; k < 2; k++)
  {
    __CPROVER_atomic_begin();
    i = i + j;
    __CPROVER_atomic_end();
  }
}

void t2(void)
{
  for(int k = 0; k < 2; k++)
  {
    __CPROVER_atomic_begin();
    j = j + i;
    __CPROVER_atomic_end();
  }
}

void t3(void)
{
  x = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: t1();
  __CPROVER_ASYNC_2: t2();
  __CPROVER_ASYNC_3: t3();
  int v = x;
  __CPROVER_assert(v <= 1, "x is 0 or 1");
  return 0;
}
