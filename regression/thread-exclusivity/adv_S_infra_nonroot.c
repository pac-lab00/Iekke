// EXPECT: VERIFICATION FAILED under --rounds; g must NOT be exclusive. A
// void *(void *) function that is not a start routine still ends up in the
// __spawned_thread dispatch, i.e. in `infra`, whose mentions are blacklisted.
//
// A void*(void*) function that is NOT a start routine still lands in the
// __spawned_thread dispatch; main also calls it and it touches g.
#include <pthread.h>
#include <assert.h>
int g = 0;
void *notaroot(void *a) { g = 99; return 0; }
void *(*keep)(void *) = notaroot;
void *t1(void *arg) { for(g = 0; g < 2; g++) {} assert(g == 2); return 0; }
int main(){ pthread_t a; pthread_create(&a,0,t1,0); notaroot(0); pthread_join(a,0); return 0; }
