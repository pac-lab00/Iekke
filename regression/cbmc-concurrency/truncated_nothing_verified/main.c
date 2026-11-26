#include <pthread.h>

// A run cut short before it generates any property is not a proof.
//
// `main` fills a 64-element array before it creates a thread. Below
// `--unwind 64` the unwinding *assumption* makes every path past the bound
// infeasible, so execution never reaches pthread_create, no shared access is
// ever recorded, and the property set comes out empty.
//
// determine_result() folds the statuses starting from PASS, so an empty set
// used to be reported as VERIFICATION SUCCESSFUL -- a proof of a program the
// tool had not looked at. On an expected-false task that is the worst answer
// available (-32 in SV-COMP) against 0 for saying nothing.
//
// `pthread/indexer` is the real instance: it initialises 128 mutexes before
// creating any thread and was answered SUCCESSFUL at every bound below 129,
// with no verification condition generated at all.

int datum;
int pad[64];

void *thread(void *arg)
{
  datum = 5;
  return 0;
}

int main(void)
{
  pthread_t id;

  for(int i = 0; i < 64; i++)
    pad[i] = i; // longer than the bound: everything below is unreachable

  pthread_create(&id, 0, &thread, 0);
  datum = 8; // races, but the bound never lets us get here

  return 0;
}
