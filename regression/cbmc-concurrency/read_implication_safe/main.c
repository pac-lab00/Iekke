// The read has to be concurrent to go through the read-from encoding at all.
//
// A read placed after pthread_join is not shared -- only one thread is live by
// then -- so it is constrained by ordinary SSA and says nothing about the
// read-from chain. The reader here runs alongside the writer, so its value for
// x comes from the encoding under test.
//
// x is only ever 0 (initial) or 1 (the single writer), so the assertion holds.
// If a read's constraint were dropped the solver would be free to invent a
// value for v and the assertion would report FAILED -- which is what makes
// this test discriminating in the direction that matters: a weakened encoding
// over-approximates, and only a safe program can catch that.

#include <pthread.h>

int x;

void *writer(void *arg)
{
  (void)arg;
  x = 1;
  return 0;
}

void *reader(void *arg)
{
  (void)arg;
  int v = x;
  __CPROVER_assert(v == 0 || v == 1, "x only ever holds 0 or 1");
  return 0;
}

int main(void)
{
  pthread_t w, r;

  pthread_create(&w, 0, writer, 0);
  pthread_create(&r, 0, reader, 0);
  pthread_join(w, 0);
  pthread_join(r, 0);

  return 0;
}
