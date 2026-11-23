// A `&T` parameter the callee writes through (here by lending it on to `push`) is held to the law
// of exclusivity as an `inout` one is: no other argument of the call may reach the same place.
#include <stdlib::vec>
struct Bag { items: Vec<long>, n: long }
add into:&Vec<long> from:&Bag -> void { into.push(from.n); }
main -> int {
    b: Bag = Bag { items: vec![1], n: 4 };
    add(&b.items, &b);
    return b.items.len() as int;
}
