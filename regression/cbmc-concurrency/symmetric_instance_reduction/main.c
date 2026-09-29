// A family of interchangeable slots, reduced to a small instance.
//
// bucket[] is symmetric: nothing relates one slot to another, and every index
// is a local chosen uniformly over the whole range. So a race that exists at
// 64 slots exists at 2, and looking for it at 2 is enough.
//
// The point of the test is that this program is only tractable *because* of
// the reduction. The setup loop runs once per slot, so at 64 slots it needs 65
// unwindings; at --unwind 4 without the reduction the loop is cut, the
// unwinding assumption prunes every path through it, and the run reports
// success having generated nothing to check (measured: "Generated 0 VCC(s)").
// With --symmetric-instance 2 the loop is two iterations long, runs to
// completion, and the race is found.
//
// That asymmetry is why this is sound as an under-approximation: a reported
// violation is real, a safe result at a reduced instance proves nothing.

#include <pthread.h>

#define N 64

extern int __VERIFIER_nondet_int(void);

int bucket[N];

void *worker(void *arg)
{
  (void)arg;

  // A local index, uniform over the family: two threads may pick the same slot
  // and race on it.
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(i >= 0 && i < N);
  bucket[i] = bucket[i] + 1;
  return 0;
}

int main(void)
{
  pthread_t a, b;

  for(int j = 0; j < N; j++)
    bucket[j] = 0;

  pthread_create(&a, 0, worker, 0);
  pthread_create(&b, 0, worker, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);

  return 0;
}
