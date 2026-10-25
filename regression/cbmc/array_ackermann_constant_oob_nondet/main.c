// A constant array: an in-bounds index reads its operand; two reads at the
// same out-of-bounds index still see the same (unconstrained) element.
const int t[100] = {1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6, 7, 1, 2};

int main()
{
  unsigned i, j;
  if(i == j)
    __CPROVER_assert(t[i] == t[j], "equal indices, equal elements");
  if(i < 100)
    __CPROVER_assert(t[i] >= 1 && t[i] <= 7, "in bounds: an operand");
  __CPROVER_assume(i < 100);
  __CPROVER_assert(t[i] == 1, "not every operand is 1");
  return 0;
}
