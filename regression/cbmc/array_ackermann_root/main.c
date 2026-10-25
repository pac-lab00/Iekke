// An array no assignment defines (a nondet local) keeps its Ackermann
// constraints: two reads at equal indices see the same element.
int main()
{
  int a[200];
  unsigned i, j;
  __CPROVER_assume(i < 200 && j < 200);
  if(i == j)
    __CPROVER_assert(a[i] == a[j], "equal indices, equal elements");
  __CPROVER_assert(a[i] == a[j], "different indices may differ");
  return 0;
}
