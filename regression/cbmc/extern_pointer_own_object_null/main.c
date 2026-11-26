// The environment's pointer may still be null: the dereference must fail.
struct S { int x; };
extern struct S *ep;
int main(void) { ep->x = 1; return 0; }
