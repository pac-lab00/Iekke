#include <pthread.h>
#include <assert.h>
extern int __VERIFIER_nondet_int(void);
struct cache { int slots[4]; pthread_mutex_t mutex[4]; } c;
int main() {
  for (int k = 0; k < 4; k++) { pthread_mutex_init(&c.mutex[k], 0); c.slots[k] = k + 1; }
  int j = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= j && j < 4);
  int k = __VERIFIER_nondet_int();
  __CPROVER_assume(0 <= k && k < 4 && k != j);
  pthread_mutex_lock(&c.mutex[j]);
  assert(c.slots[0] == 1 && c.slots[1] == 2 && c.slots[2] == 3 && c.slots[3] == 4);
  assert(pthread_mutex_trylock(&c.mutex[k]) == 0);
  assert(pthread_mutex_trylock(&c.mutex[j]) == 0);
  return 0;
}
