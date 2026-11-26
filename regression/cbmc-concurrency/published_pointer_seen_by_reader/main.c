// A pointer published by a thread symexed later must still be visible here.
//
// Value sets are built in symex order. `reader` runs first, so when it
// executes `p = gp` the only target `gp` has is `&n1`: `updater` has not been
// symexed yet and `&n2` does not exist in any value set. The dereference
// `p->x` then resolves against `n1` alone, the interleaving in which the
// reader runs after the publication is never encoded, and `obs == 7` looks
// unreachable.
//
// Under sequential consistency that interleaving is perfectly real, so the
// assertion must fail. This is CBMC issue #305.

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
  gp = &n2; // published after the reader was symexed
  cnt++;
}

int main(void)
{
  __CPROVER_ASYNC_0:
  reader();
  __CPROVER_ASYNC_1:
  updater();
  __CPROVER_assume(cnt == 2);
  __CPROVER_assert(obs != 7, "obs must not be 7");
  return 0;
}
