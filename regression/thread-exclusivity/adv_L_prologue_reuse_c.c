// EXPECT: VERIFICATION FAILED under --rounds. Debug must show h NOT in the
// prologue set and g rejected with "2 roots". This is the context-sensitive
// prologue regression: before the fix, h was in the prologue because it is
// reachable from __CPROVER_initialize, which suppressed main's POST-SPAWN
// write to g and wrongly reported SUCCESSFUL.
//
// CONFIRMED SOUNDNESS BUG (pure C).
// main writes g AFTER spawning t1, but only through helper h().
// h() is also reachable from __CPROVER_initialize (via a gcc
// __attribute__((constructor)) function), which puts h into the analysis
// "prologue" set. prologue membership then suppresses ALL of the initial
// thread s mentions of h -- including the post-spawn call h(99) -- so g is
// wrongly reported thread-exclusive to t1 and the race is silently dropped.
#include <pthread.h>
#include <assert.h>

int g = 0;
int other = 0;

void h(int v) { g = v; }

__attribute__((constructor)) static void myinit(void) { h(0); }

void *t1(void *arg)
{
  for(g = 0; g < 2; g++) {}
  assert(g == 2);
  return 0;
}

void *t2(void *arg) { other = 7; return 0; }

int main()
{
  pthread_t a, b;
  pthread_create(&a, 0, t1, 0);
  pthread_create(&b, 0, t2, 0);
  h(99);                 // races with t1
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
