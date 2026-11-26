// x only lends its address to set, which only dereferences it: no pointer to
// x is left when x dies, so its death is not recorded
void set(int *p)
{
  *p = 1;
}

int f(void)
{
  int x;
  set(&x);
  return x;
}

int main(void)
{
  return f();
}
