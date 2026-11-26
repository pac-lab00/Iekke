#include <pthread.h>
void reach_error(void){ __assert_fail("0","f",1,"f"); }
int flag, data;
void *w(void *a){ data = 1; flag = 1; return 0; }
void *r(void *a){ while(!flag) {} if(data != 1) reach_error(); return 0; }
int main(){ pthread_t a,b; pthread_create(&a,0,w,0); pthread_create(&b,0,r,0); return 0; }
