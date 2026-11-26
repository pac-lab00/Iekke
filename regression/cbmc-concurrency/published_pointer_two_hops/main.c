// A pointer published through a relay thread, read by a thread symexed first.
//
// CBMC issue #305 needs more than one extra symex pass when a publication
// travels through another thread. The threads are symexed in spawn order:
// reader, relay, updater. Each pass tops up a shared read of a pointer from
// the points-to sets collected by the previous one, so the updater's &n2
// reaches the relay's read of g2 in the second pass, and only then the
// relay's store g1 = q carries &n2 into g1's set. The reader's read of g1
// learns it in a third pass. A fixed second pass resolved p->x against n1
// alone, and the interleaving updater, relay, reader -- where obs == 7 -- was
// never encoded. libvsync/cnalock hands its secondary queue over the same
// way, through two threads, and a dereference of the stale node gave a false
// valid-memsafety violation.
#include <assert.h>

struct s
{
  int x;
};

struct s n1 = {0}, n2 = {0};
struct s *g1 = &n1, *g2 = &n1;
int obs = -1, cnt = 0;

void reader(void)
{
  struct s *p = g1;
  obs = p->x;
  cnt++;
}

void relay(void)
{
  struct s *q = g2;
  g1 = q;
  cnt++;
}

void updater(void)
{
  n2.x = 7;
  g2 = &n2;
  cnt++;
}

int main(void)
{
__CPROVER_ASYNC_0:
  reader();
__CPROVER_ASYNC_1:
  relay();
__CPROVER_ASYNC_2:
  updater();
  __CPROVER_assume(cnt == 3);
  assert(obs != 7);
  return 0;
}
