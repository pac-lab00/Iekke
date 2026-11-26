// main's writes before the first spawn, as --array-rf folds them.
//
// A read in a spawned thread comes after all of main's prologue in any
// schedule, so --array-rf folds the prologue writes once per read, in program
// order and on whether each one ran, instead of selecting them per round. Two
// things that fold has to keep: the last prologue write wins (a[1] is 4, not
// 3, until the writer's 9), and a write on a path not taken does not count
// (a[0] is 7 only where c holds).

#include <pthread.h>
#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

int *a;
int c, x, y;

void *writer(void *arg)
{
  (void)arg;
  a[1] = 9;
  return 0;
}

void *reader(void *arg)
{
  (void)arg;
  x = a[1];
  y = a[0];
  return 0;
}

int main(void)
{
  int size = __VERIFIER_nondet_int();
  __CPROVER_assume(size >= 2 && size <= 3);
  a = malloc(size * sizeof(int));
  if(!a)
    abort();
  for(int i = 0; i < size; i++)
    a[i] = 0;
  c = __VERIFIER_nondet_int();
  if(c)
    a[0] = 7;
  a[1] = 3;
  a[1] = 4;
  pthread_t w, r;
  pthread_create(&w, 0, writer, 0);
  pthread_create(&r, 0, reader, 0);
  pthread_join(w, 0);
  pthread_join(r, 0);
  __CPROVER_assert(x == 4 || x == 9, "a[1] holds main's last write or the writer's");
  __CPROVER_assert(y == (c ? 7 : 0), "a[0] is 7 exactly where main wrote it");
  return 0;
}
