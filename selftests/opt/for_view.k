// `for x in b` over a type implementing `AsSlice<T>` is the bare index loop a slice's is: its
// `asSlice` inlines, and nothing is called or checked per element.
// ir-lacks: for_view::sumb call
// ir-lacks: for_view::sumb panicIndex
// ir-lacks: for_view::sumb bounds
#include <stdlib::vec>
trait AsSlice<T> { asSlice &self -> [T]; }
struct Bag { items: Vec<long> }
methods Bag for AsSlice<long> {
    asSlice &self -> [long] { unsafe { return self.items.buf.ptr[..self.items.count]; } }
}
sumb b:Bag -> long { s: long = 0; for x in b { s = s + x; } return s; }
main -> int {
    b: Bag = Bag { };
    for i in 0..10 { b.items.push(i); }
    if (sumb(b) != 45) { return 1; }
    return 0;
}
