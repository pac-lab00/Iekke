int g1, g2;

void worker(void)
{
  g1 = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: worker();
  g2 = 2;
  return 0;
}
