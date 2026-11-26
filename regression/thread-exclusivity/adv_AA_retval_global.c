// EXPECT: VERIFICATION FAILED under --rounds; g rejected with "2 roots".
// remove_returns introduces f#return_value, a shared static-lifetime symbol
// written by both threads.
//
// remove_returns creates f#return_value, a shared static-lifetime global.
#include <pthread.h>
#include <assert.h>
int g = 0;
int f(int x){ return x + 1; }
void *t1(void *arg){ int v = 0; while(v < 2) v = f(v); g = v; assert(g == 2); return 0; }
void *t2(void *arg){ f(41); g = 99; return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); pthread_join(a,0); pthread_join(b,0); return 0; }
