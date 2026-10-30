unsigned nondet_unsigned(void);
int obj[2];
int *arr[64];
int main(void)
{
  unsigned i = nondet_unsigned();
  __CPROVER_assume(i < 64);
  arr[i] = &obj[1];
  unsigned long long w = (unsigned long long)arr[i];
  unsigned short s = (unsigned short)arr[i];
  __CPROVER_assert((unsigned short)w == s, "same pointer, same bits");
  return 0;
}
