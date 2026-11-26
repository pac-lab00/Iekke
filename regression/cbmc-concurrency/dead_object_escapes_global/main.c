// the address of x is stored in a global: dereferencing it after f returns
// is a dead-object violation
int *g;

void f(void)
{
  int x = 1;
  g = &x;
}

int main(void)
{
  f();
  return *g;
}
