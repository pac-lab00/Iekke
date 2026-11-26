// `g` is a global, so goto-symex marks every access to it shared the moment a
// second thread exists -- even though only main ever touches it. Sharedness is
// decided per program, never per object, so without --thread-private `g` gets
// a full rounds-deep lazy chain to express a read-from that main's own program
// order already fixes.
//
// The assertion is what makes this discriminating: it pins down that the read
// sees the LAST write before it in program order, under that write's guard. A
// static chain that picked the wrong link -- the first write, or one from the
// wrong branch -- would report a violation this program does not have.

#include <pthread.h>

int g;

void *worker(void *arg)
{
  (void)arg; // deliberately touches nothing: g must stay single-threaded
  return 0;
}

int main(void)
{
  pthread_t t;

  pthread_create(&t, 0, worker, 0);

  g = 1;
  g = 2;
  if(__VERIFIER_nondet_int())
    g = 3;

  __CPROVER_assert(g == 2 || g == 3, "g holds its last executed write");

  pthread_join(t, 0);
  return 0;
}
