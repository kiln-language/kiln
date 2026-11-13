// A struct literal's field is held to its declared type: a `Node` is not a `Box<Node>`.
#include <stdlib::heap>
struct Node { v: long }
struct Holder { b: Box<Node> }
main -> int { n: Node = Node { v: 3 }; h: Holder = Holder { b: n }; return 0; }
