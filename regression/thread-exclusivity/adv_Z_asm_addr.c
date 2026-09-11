// EXPECT: the front end refuses this file outright ("Deagle does not support
// asm code"), i.e. it fails closed and never reaches the analysis. Kept as a
// regression guard: if inline asm ever becomes supported, this must be
// rechecked, because the only thing stopping g from looking exclusive is
// dirtyt seeing the address-of inside the asm statement.
// NOTE: no VERIFICATION verdict is produced by design; do not treat the
// missing verdict as a pass/fail signal for the other tests.
//
// Does dirtyt see an address-of that only occurs inside inline asm?
#include <pthread.h>
#include <assert.h>
int g = 0;
int *volatile p;
void *t1(void *arg){ for(g=0;g<2;g++){} assert(g==2); return 0; }
void *t2(void *arg){ __asm__ volatile("mov %1,%0" : "=r"(p) : "r"(&g)); if(p) *p = 99; return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); pthread_join(a,0); pthread_join(b,0); return 0; }
