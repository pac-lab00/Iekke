// keep copies the pointer it is given, so x does not only lend its address
int *g;

void keep(int *p)
{
  g = p;
}

void f(void)
{
  int x = 1;
  keep(&x);
}

int main(void)
{
  f();
  return *g;
}
