// A method in a bounded block (`methods Bag<T: Copy>`) is neither checked nor stamped for an
// instance that does not meet the bound (`Bag<Tree>`, whose `Tree` owns a `Bag<Tree>`): its body
// cannot run for that T (STDLIB_REVIEW gap 36). Exit code 1 + 1 = 2.
#include <stdlib::vec>
struct Bag<T> { v: Vec<T> }
methods Bag<T> { add &self x:T -> void { self.v.push(x); } size &self -> long { return self.v.len(); } }
methods Bag<T: Copy> { extend2 &self other:&Bag<T> -> void { for x in other.v { self.v.push(x); } } }
enum Tree { Leaf(long), Many(Bag<Tree>) }
main -> int {
    b: Bag<Tree> = Bag<Tree> { v: vec![] };
    b.add(Tree.Leaf(3));
    c: Bag<long> = Bag<long> { v: vec![] };
    c.add(4);
    d: Bag<long> = Bag<long> { v: vec![] };
    d.extend2(c);
    return (b.size() + d.size()) as int;
}
