// A thread whose callee ends in an assume: the guard summary must keep the
// assumption. The race on y exists only when f() returns with c != 0.
#include <pthread.h>
int x, y, c;
int nondet(void);
void f(void) { c = nondet(); if(c == 0) __CPROVER_assume(0); x = 1; }
void *t(void *a) { f(); y = 1; return 0; }
int main(void) { pthread_t id; pthread_create(&id, 0, t, 0); y = 2; pthread_join(id, 0); return 0; }
