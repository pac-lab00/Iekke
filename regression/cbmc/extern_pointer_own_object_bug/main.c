// Reads and writes through it agree.
struct S { int x; int y; };
extern struct S *ep;
int main(void) {
  if(ep) { ep->x = 5; ep->y = 7; __CPROVER_assert(ep->x == 6, "kept"); }
  return 0;
}
