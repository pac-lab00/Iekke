// A string passed through a char pointer used to become the assumption
// arg0 = { 15, '%', 's', ... }: a brace list is no C expression, and CPAchecker
// rejected the whole witness on it (w83977af_ir, nsc-ircc).
#include <assert.h>
int printed;
int say(const char *arg0, ...)
{
  printed = arg0[1];
  return 0;
}
int main(void)
{
  say("\017%s()\n", "open");
  assert(printed != 37);
  return 0;
}
