// A large array that the bounded execution barely touches.
//
// convert_index used to call map.get_literals on the array symbol purely to
// "record type if array is a symbol", on the path where the array decision
// procedure handles the array and nothing is bit-blasted. get_literals
// allocates one SAT variable per bit as a side effect, so this 10000-element
// array cost 320000 variables for every SSA version of it -- variables that
// never appear in a single clause.
//
// The test is the variable count in the statistics line: the encoding of this
// program is a few tens of thousands of variables, and was millions.

#include <assert.h>
#include <pthread.h>

pthread_t ids[10000];
int shared;

void *worker(void *arg)
{
  (void)arg;
  shared = 1;
  return 0;
}

int main(void)
{
  for(int i = 0; i < 2; i++)
    pthread_create(&ids[i], 0, worker, 0);
  for(int i = 0; i < 2; i++)
    pthread_join(ids[i], 0);

  assert(shared == 0 || shared == 1);
  return 0;
}
