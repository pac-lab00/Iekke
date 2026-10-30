unsigned char nondet_uchar(void);
signed char nondet_schar(void);
struct bf { signed int s1 : 1; signed int s2 : 1; unsigned u1 : 1; unsigned u2 : 1; };
int main(void)
{
  unsigned char x = nondet_uchar(), y = nondet_uchar();
  signed char a = nondet_schar(), b = nondet_schar();
  /* partly constant operands: shared constant prefixes, differing constant bits */
  unsigned char xl = x & 0x0f, yh = y | 0xf0, xm = (x & 0x3c) | 0x40, ym = (y & 0x3f) | 0x40;
  __CPROVER_assert((xl < yh) == ((int)xl - (int)yh < 0), "u lt const prefix");
  __CPROVER_assert((xm <= ym) == ((int)xm - (int)ym <= 0), "u le common prefix");
  __CPROVER_assert((xm < ym) == ((int)xm - (int)ym < 0), "u lt common prefix");
  __CPROVER_assert((x < y) == ((int)x - (int)y < 0), "u lt");
  __CPROVER_assert((x <= y) == ((int)x - (int)y <= 0), "u le");
  __CPROVER_assert((x <= x) && !(x < x), "u self");
  signed char ap = a & 0x7f, bn = b | (signed char)0x80, as = (a & 0x0f) | (signed char)0x80;
  __CPROVER_assert((ap < bn) == ((int)ap - (int)bn < 0), "s lt sign const");
  __CPROVER_assert((bn <= ap) == ((int)bn - (int)ap <= 0), "s le sign const");
  __CPROVER_assert((as < bn) == ((int)as - (int)bn < 0), "s lt both neg");
  __CPROVER_assert((a < ap) == ((int)a - (int)ap < 0), "s lt one sign const");
  __CPROVER_assert((a < b) == ((int)a - (int)b < 0), "s lt");
  __CPROVER_assert((a <= b) == ((int)a - (int)b <= 0), "s le");
  /* x < 5 style */
  __CPROVER_assert((x < 5) == (x == 0 || x == 1 || x == 2 || x == 3 || x == 4), "u lt 5");
  __CPROVER_assert((a >= -2) == (a == -2 || a == -1 || a >= 0), "s ge -2");
  struct bf f;
  f.s1 = nondet_schar(); f.s2 = nondet_schar(); f.u1 = nondet_uchar(); f.u2 = nondet_uchar();
  int c1 = f.s1 < f.s2, c2 = f.u1 <= f.u2;
  __CPROVER_assert(c1 == ((int)f.s1 - (int)f.s2 < 0), "1-bit signed lt");
  __CPROVER_assert(c2 == ((int)f.u1 - (int)f.u2 <= 0), "1-bit unsigned le");
  /* reachable: must FAIL */
  __CPROVER_assert(!(xm < ym && ym - xm == 3), "reach");
  return 0;
}
