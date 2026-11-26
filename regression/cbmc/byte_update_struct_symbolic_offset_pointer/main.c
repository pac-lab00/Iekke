#include <assert.h>
_Bool nondet_bool(void);
struct node { void *lock; struct node *parent; unsigned a, b, c; };
struct { struct node nodes[8]; } s;
int x;
int main() {
  s.nodes[1].parent = &s.nodes[0];
  s.nodes[2].parent = &s.nodes[1];
  struct node *p = nondet_bool() ? &s.nodes[1] : &s.nodes[2];
  p->lock = &x;
  assert(s.nodes[1].parent == &s.nodes[0]);
  assert(s.nodes[2].parent == &s.nodes[1]);
  return 0;
}
