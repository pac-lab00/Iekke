// The only read of g is inside a check; a thread writes g: a race.
#include <pthread.h>
int g;
void *t(void *a) { g = 1; return 0; }
int main(void) {
  pthread_t th; pthread_create(&th, 0, t, 0);
  __CPROVER_precondition(g == 0, "a check that reads g");
  pthread_join(th, 0);
  return 0;
}
