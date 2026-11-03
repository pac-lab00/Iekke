int x = 5;

void worker(void)
{
  int a = x;
  __CPROVER_assert(a == 5, "a");
}

int main(void)
{
  __CPROVER_ASYNC_1: worker();
  int b = x;
  __CPROVER_assert(b == 5, "b");
  return 0;
}
