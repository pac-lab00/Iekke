// Main joins the second thread and then expects both to be done. That fails
// when the second has run and the first has not: a join that sees one of the
// two exited and not the other tells them apart, so no ordering may forbid
// the schedule. The write to started keeps the front end from turning
// create(b); join(b) into a plain call.

#include <assert.h>
#include <pthread.h>

int done, started;

void *body(void *arg)
{
  (void)arg;
  __CPROVER_atomic_begin();
  done++;
  __CPROVER_atomic_end();
  return 0;
}

int main(void)
{
  pthread_t a, b;
  pthread_create(&a, 0, body, 0);
  pthread_create(&b, 0, body, 0);
  started = 1;
  pthread_join(b, 0);
  assert(done == 2);
  return 0;
}
