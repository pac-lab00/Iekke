int x;

void worker(void)
{
  x = 1;
}

int main(void)
{
  __CPROVER_ASYNC_1: worker();
  int seen = x;
  __CPROVER_assert(seen == 0 || seen == 1, "seen");
  return 0;
}
