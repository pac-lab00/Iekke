int x;

void worker(void)
{
  x = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: worker();
  __CPROVER_assert(x == 0, "main reads x after the worker wrote it");
  return 0;
}
