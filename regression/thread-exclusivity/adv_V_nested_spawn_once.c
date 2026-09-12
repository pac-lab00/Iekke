// EXPECT: VERIFICATION FAILED under --rounds; g rejected with "2 roots".
// A spawned thread spawns two further threads that share g.
//
// t1 spawns t2 exactly once; g is only syntactically touched by t2.
#include <pthread.h>
#include <assert.h>
int g = 0;
void *t2(void *arg){ for(g=0;g<2;g++){} assert(g==2); return 0; }
void *t3(void *arg){ g = 99; return 0; }
void *t1(void *arg){ pthread_t b,c; pthread_create(&b,0,t2,0); pthread_create(&c,0,t3,0); return 0; }
int main(){ pthread_t a; pthread_create(&a,0,t1,0); pthread_join(a,0); return 0; }
