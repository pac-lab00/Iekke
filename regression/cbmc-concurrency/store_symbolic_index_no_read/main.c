#include <pthread.h>

// A store does not read the array it stores into.
//
// Each thread takes a distinct ticket with an atomic fetch-add and writes the
// slot that ticket names, so no two threads ever touch the same element and
// the program is race-free.
//
// A field-sensitive array lowers `slot[i] = 1` to, for every element k,
//
//     slot[[k]] == (i == k ? 1 : slot[[k]])
//
// and building that right-hand side materialises the whole array, renaming
// every element, which emitted a shared READ of every element. The program
// reads nothing there -- those reads are the lowering framing the untouched
// elements back over themselves -- but race detection is the only consumer of
// the event set, so a thread storing to slot[1] was recorded as reading
// slot[0], which another thread stores to. The counterexample named the pair
// plainly: "racing read in thread 1" against "racing write in thread 2".
//
// The write half was already conditioned on `i == k`; the reads now record no
// event at all, which is what record_events exists for -- the value is still
// produced, so this thread's own view of the array is unchanged.

int phead = 0;
int slot[4];

void *thread(void *arg)
{
  int curr = __atomic_fetch_add(&phead, 1, __ATOMIC_SEQ_CST);
  slot[curr % 4] = 1; // a distinct element per thread
  return 0;
}

int main(void)
{
  pthread_t a, b;

  pthread_create(&a, 0, &thread, 0);
  pthread_create(&b, 0, &thread, 0);
  pthread_join(a, 0);
  pthread_join(b, 0);

  return 0;
}
