/* A __CPROVER_ASYNC spawn whose callee takes the address of a local of the
   spawning function. symex emits the copy of that local into the new thread's
   frame -- a step tagged with the new thread's number -- while main still has
   steps to come. Inferring "thread ended" from a rise in source.thread_nr used
   to mark main inactive at its own spawn statement, so main was never
   scheduled again and everything after the spawn became unreachable. The
   assertion below is trivially reachable and must be reported. */
int g;

void *reader(void *p)
{
  g = *((unsigned int *)p);
  return 0;
}

int main(void)
{
  unsigned int local = 7;
__CPROVER_ASYNC_0:
  reader(&local);
  assert(0); /* main must still be schedulable after the spawn */
  return 0;
}
