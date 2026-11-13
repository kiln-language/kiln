// A callee reaches the vector through the struct that holds it and clears it. The length the
// loop compared against was read before the call; the read after it must still be checked.
#include <stdlib::vec>
struct Bag { v: Vec<long>, n: long }
empty inout b:Bag -> void { b.v.clear(); b.n = 0; }
main -> int {
    b: Bag = Bag { v: vec![1, 2, 3], n: 3 };
    s: long = 0;
    i: long = 0;
    while (i < b.v.len()) {
        x: long = b.v.get(i);
        if (x == 2) { empty(&b); }
        s = s + b.v.get(i);
        i = i + 1;
    }
    return s as int;
}
