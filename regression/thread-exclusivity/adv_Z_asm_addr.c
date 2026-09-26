// EXPECT: the tool refuses this file and produces no verdict (EXIT=6,
// "inline asm writing a pointer operand"). It fails closed, by design.
//
// Inline asm in general IS analysed now: goto_asm no longer exits at the first
// asm statement, remove_asm havocs the outputs of asm it cannot translate, and
// an untranslated asm is left in the goto program so dirtyt can still see the
// address-of inside it. What is still refused is the narrow case this file
// exercises, an asm whose *output* is a pointer:
//
//   __asm__ volatile("mov %1,%0" : "=r"(p) : "r"(&g));
//   if (p) *p = 99;
//
// side_effect_expr_nondett of pointer type yields a fresh abstract object, not
// a points-to set containing the addresses the asm was given, so the write
// through p lands somewhere unrelated and t1's assert(g==2) passes. Confirmed
// with LAZYPO_ACCESS_DEBUG: g was correctly shared, but the write went to
// p$object. Until that is modelled, refusing beats answering wrongly.
//
// So this stays a guard in both directions. A verdict of any kind here means
// the pointer case became analysable and must be rechecked; a SUCCESSFUL in
// particular is a missed bug, since t2 does write g through p.
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
