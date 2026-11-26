unsigned nondet_unsigned(void);
int main(void)
{
  unsigned d = 7, n = 1000, z = 0;
  int sn = -1000, sd = 7;
  unsigned x = nondet_unsigned();
  __CPROVER_assert(n / d == 142, "udiv");
  __CPROVER_assert(n % d == 6, "urem");
  __CPROVER_assert(sn / sd == -142, "sdiv");
  __CPROVER_assert(sn % sd == -6, "srem");
  __CPROVER_assert((n / d) * x == 142 * x, "folded multiply");
  unsigned q = n / z; /* division by zero: unconstrained, both outcomes */
  __CPROVER_assert(q != 5, "div by zero may be 5");
  return 0;
}
