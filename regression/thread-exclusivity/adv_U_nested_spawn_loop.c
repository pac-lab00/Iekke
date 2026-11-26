// EXPECT: VERIFICATION FAILED under --rounds; g rejected with "2 roots".
// A spawned thread spawns further threads, in a loop.
//
// t1 spawns t2 in a loop; t2 is the only syntactic toucher of g.
#include <pthread.h>
#include <assert.h>
int g = 0;
void *t2(void *arg) { g++; return 0; }
void *t1(void *arg) {
  pthread_t b; int i;
  for(i = 0; i < 2; i++) pthread_create(&b,0,t2,0);
  return 0;
}
int main(){ pthread_t a; pthread_create(&a,0,t1,0); pthread_join(a,0); assert(g <= 1); return 0; }
