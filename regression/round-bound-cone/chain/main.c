int i = 1, j = 1, x = 0;
int a = 1, b = 1;

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
  x = j;
}

void t4(void)
{
  for(int k = 0; k < 5; k++)
  {
    __CPROVER_atomic_begin();
    a = a + b;
    __CPROVER_atomic_end();
  }
}

void t5(void)
{
  for(int k = 0; k < 5; k++)
  {
    __CPROVER_atomic_begin();
    b = b + a;
    __CPROVER_atomic_end();
  }
}

int main(void)
{
  __CPROVER_ASYNC_1: t1();
  __CPROVER_ASYNC_2: t2();
  __CPROVER_ASYNC_3: t3();
  __CPROVER_ASYNC_4: t4();
  __CPROVER_ASYNC_5: t5();
  int v = x;
  __CPROVER_assert(v != 8, "j reaches 8 only through four alternations");
  return 0;
}
