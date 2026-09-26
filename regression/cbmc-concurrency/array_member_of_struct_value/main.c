// An array that is a member of a struct *value* rather than of a symbol.
// add_array_constraints had a case for member-of-symbol, which needs no
// constraints because such an array is its own object, but none for this, so
// it fell through to the closing invariant and aborted the run:
//
//   unexpected array expression (add_array_constraints): 'member' over 'struct'
//
// It is only reachable once arrays-uf=auto is honoured, since that keeps
// arrays as array expressions instead of bit-blasting them -- so this also
// guards the arrays-uf change, whose own effect is on speed rather than on
// any verdict and cannot be regression-tested directly.
//
// Extending the member-of-symbol no-op to cover this would have been wrong: a
// member of a struct value IS the corresponding component, so leaving it
// unconstrained lets the solver choose contents the component does not have.
// It is constrained elementwise against that component instead.
//
// Reduced from sv-benchmarks goblint-regression/09-regions_19-nested_nr-deref.c
// against a binary with arrays-uf but without the fix. What is load-bearing is
// a global struct holding an array whose element type is a union
// (pthread_mutex_t), written via pthread_mutex_init so the assignment is of a
// whole struct value, and indexed nondeterministically. Dropping the linked
// list from the original still reproduces it; dropping the mutex array does
// not.
//
// Verified to discriminate:
//   without the fix   EXIT=134, SIGABRT, invariant above
//   with the fix      EXIT=0,   VERIFICATION SUCCESSFUL

#include <pthread.h>
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);
static void assume(int c) { if(!c) abort(); }

struct cache
{
  int *slots[10];
  pthread_mutex_t mutex[10];
} c;

static void *t_fun(void *arg)
{
  (void)arg;
  int i = __VERIFIER_nondet_int();
  assume(0 <= i && i < 10);
  pthread_mutex_lock(&c.mutex[i]);
  c.slots[i] = malloc(sizeof(int));
  pthread_mutex_unlock(&c.mutex[i]);
  return 0;
}

int main(void)
{
  for(int i = 0; i < 10; i++)
    pthread_mutex_init(&c.mutex[i], 0);

  int j = __VERIFIER_nondet_int();
  assume(0 <= j && j < 10);

  pthread_t id;
  c.slots[j] = malloc(sizeof(int));
  pthread_create(&id, 0, t_fun, 0);
  pthread_mutex_lock(&c.mutex[j]);
  int d = *c.slots[j];
  (void)d;
  pthread_mutex_unlock(&c.mutex[j]);
  return 0;
}
