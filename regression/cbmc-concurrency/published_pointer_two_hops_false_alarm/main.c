// The false-alarm side of published_pointer_two_hops: same relay, opposite
// symptom.
//
// Once the relay is done, g1 points to n2 or n3, and both link to
// themselves, so p->next is never NULL. The reader is symexed first and
// learns what g1 may point to only from the sets collected by earlier
// passes; &n2 reaches g1 through the relay, so it is known only after two of
// them. With a fixed second pass p->next was resolved against n1 and n3
// alone, and when p is &n2 the read returned an unconstrained value: the
// dereference q->x was reported as a NULL-pointer dereference. This is the
// shape of the false valid-memsafety violation in libvsync/cnalock.

struct s
{
  struct s *next;
  int x;
};

struct s n1 = {0, 0}, n2 = {0, 0}, n3 = {&n3, 0};
struct s *g1 = &n1, *g2 = &n3;
int done = 0;

void reader(void)
{
  if(done)
  {
    struct s *p = g1;
    struct s *q = p->next;
    q->x = 1;
  }
}

void relay(void)
{
  struct s *q = g2;
  g1 = q;
  done = 1;
}

void updater(void)
{
  n2.next = &n2;
  g2 = &n2;
}

int main(void)
{
__CPROVER_ASYNC_0:
  reader();
__CPROVER_ASYNC_1:
  relay();
__CPROVER_ASYNC_2:
  updater();
  return 0;
}
