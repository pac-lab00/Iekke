// CBMC issue #305, in the configuration that ships -- no flag.
//
// Value sets are built in symex order, which for a concurrent program is not
// an execution order. The reader is spawned first, so it is symexed first,
// and the pointer the updater publishes later is not in its set: the
// dereference resolves against the stale entry and the interleaving is never
// encoded. Under sequential consistency the reader can run after the updater,
// so obs == 7 is reachable and this assertion must fail.
//
// The companion test published_pointer_seen_by_reader covers the same defect
// with --refined-pointer-analysis; this one pins the default configuration,
// where the repair was dead code until the second symex pass was added.
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
