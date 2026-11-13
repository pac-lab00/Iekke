#include <pthread.h>
#include <stdlib.h>
int *G1, *G2; int s1, s2;
void *t1(void *a){ for(int i=0;i<4;i++) s1 += G1[i]; G2[0] = 9; return 0; }
void *t2(void *a){ for(int i=0;i<4;i++) s2 += G1[i]; return 0; }
int main(){ G1 = malloc(16); G2 = malloc(4); for(int i=0;i<4;i++) G1[i]=i; pthread_t a,b; pthread_create(&a,0,t1,0); pthread_create(&b,0,t2,0); pthread_join(a,0); pthread_join(b,0); return s1+s2+G2[0]; }
