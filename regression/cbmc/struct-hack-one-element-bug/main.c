// As struct-hack-one-element, with an assertion that must fail: data[1]
// holds the value written to it.
#include <assert.h>
#include <stdlib.h>
struct Foo { int i; char data[1]; };
int main()
{
  struct Foo *foo = malloc(sizeof(struct Foo) + sizeof(char) * 2);
  assert(foo);
  foo->data[0] = 'a';
  foo->data[1] = 'b';
  assert(foo->data[1] == 'x');
  foo->data[2] = 'c';
  assert(foo->data[1] == 'x');
  return 0;
}
