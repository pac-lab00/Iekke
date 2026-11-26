/* The verify-treercu (Linux Tree RCU) shape, reduced: two __CPROVER_ASYNC
   spawns whose callees take the address of a local of main, a join modelled by
   an assume on a counter, and the message-passing property. With the
   grace period removed the violation is reachable under sequential
   consistency: the reader reads x (0), the updater then runs x=1; y=1, and the
   reader reads y (1).

   When main was marked inactive at its first spawn, the second thread was
   never created, __CPROVER_assume(cnt == 2) was unsatisfiable, and this
   reported VERIFICATION SUCCESSFUL vacuously -- which is exactly how the whole
   verify-treercu benchmark appeared to verify. */
int x, y, tpr_x, tpr_y, cnt;

void *updater(void *p)
{
  (void)p;
  x = 1;
  y = 1;
  cnt++;
  return 0;
}

void *reader(void *p)
{
  (void)p;
  tpr_x = x;
  tpr_y = y;
  cnt++;
  return 0;
}

int main(void)
{
  unsigned int id0 = 0, id1 = 1;
__CPROVER_ASYNC_0:
  updater(&id0);
__CPROVER_ASYNC_1:
  reader(&id1);
  __CPROVER_assume(cnt == 2);
  assert(tpr_y == 0 || tpr_x == 1);
  return 0;
}
