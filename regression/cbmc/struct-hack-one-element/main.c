// The struct hack: a one-element array at the end of a struct, in a block
// allocated with room for more. data[1] lies past the declared end but inside
// the block; it used to be read and written inside the cell of data[0].
#include <assert.h>
#include <stdlib.h>
struct Foo { int i; char data[1]; };
int main()
{
  struct Foo *foo = malloc(sizeof(struct Foo) + sizeof(char) * 2);
  assert(foo);
  foo->data[0] = 'a';
  foo->data[1] = 'b';
  assert(foo->data[1] == 'b');
  foo->data[2] = 'c';
  assert(foo->data[1] == 'b');
  return 0;
}
