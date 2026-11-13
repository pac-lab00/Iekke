#include <pthread.h>
#include <assert.h>

// the store changes memory on every pass, so no pass may be cut: the loop
// runs three times before the assertion fails, which two unwindings cannot
// cover
int count;

int main()
{
  while(__atomic_load_n(&count, __ATOMIC_SEQ_CST) < 3)
    __atomic_store_n(&count, count + 1, __ATOMIC_SEQ_CST);
  assert(count != 3);
  return 0;
}
