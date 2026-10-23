struct T { int x; } t0;
struct T *current_task = &t0;
static struct T *get_current(void)
{
  struct T *pfo_ret__;
  __asm__("movq %%gs:%P1,%0" : "=r"(pfo_ret__) : "p"(&current_task));
  return pfo_ret__;
}
int main(void)
{
  struct T *c = get_current();
  c->x = 1;
  __CPROVER_assert(t0.x == 2, "the asm returned the task pointer");
  return 0;
}
