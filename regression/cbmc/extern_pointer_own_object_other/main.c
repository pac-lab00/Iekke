// Not touched: an extern int, and an extern pointer to int.
extern int ei; extern int *ip;
int main(void) { if(ip) { *ip = 3; __CPROVER_assert(*ip == 3, "kept"); } __CPROVER_assert(ei == 0, "may fail"); return 0; }
