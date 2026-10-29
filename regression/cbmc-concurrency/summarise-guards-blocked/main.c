// The callee always blocks: no event after the call may happen, so no race.
#include <pthread.h>
int y;
void f(void) { __CPROVER_assume(0); }
void *t(void *a) { f(); y = 1; return 0; }
int main(void) { pthread_t id; pthread_create(&id, 0, t, 0); y = 2; pthread_join(id, 0); return 0; }
