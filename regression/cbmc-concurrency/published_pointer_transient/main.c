// A pointer published for one step, read by a thread symexed before it.
//
// The reader is spawned first, so symex resolves its *gp against the
// points-to set collected over the whole first pass. The updater points gp at
// n2 for a single step before moving it to n1, and the reader can run in
// between: obs == 7 is reachable. The collected set is built by merging each
// step's value set into it, only what changed since the previous step, so
// every step has to be merged: missing the one where gp holds &n2 leaves the
// reader unable to see n2, and the failure is reported SUCCESSFUL.

#include <assert.h>

struct s
{
  int x;
};

struct s n1 = {0}, n2 = {0};
struct s *gp = &n1;
int obs = -1, cnt = 0;

void reader(void)
{
  struct s *p = gp;
  obs = p->x;
  cnt++;
}

void updater(void)
{
  n2.x = 7;
  gp = &n2;
  gp = &n1;
  cnt++;
}

int main(void)
{
__CPROVER_ASYNC_0:
  reader();
__CPROVER_ASYNC_1:
  updater();
  __CPROVER_assume(cnt == 2);
  assert(obs != 7);
  return 0;
}
