#include <pthread.h>
#include <stdlib.h>
void *t(void *a){ static int c; c++; return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,t,0); pthread_create(&b,0,t,0); return 0; }
