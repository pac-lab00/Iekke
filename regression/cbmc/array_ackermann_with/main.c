// A version defined by an update keeps no Ackermann constraints of its own;
// they follow from the update and from the root's.
int main()
{
  int a[200];
  unsigned i, j, k;
  __CPROVER_assume(i < 200 && j < 200 && k < 200);
  a[k] = 5;
  if(i == k)
    __CPROVER_assert(a[i] == 5, "the updated element");
  if(i == j)
    __CPROVER_assert(a[i] == a[j], "equal indices, equal elements");
  __CPROVER_assert(a[i] == 5, "other elements are unconstrained");
  return 0;
}
