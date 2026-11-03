int x;

void worker(void)
{
  x = 2;
}

int main(void)
{
  x = 1;
  __CPROVER_ASYNC_1: worker();
  return 0;
}
