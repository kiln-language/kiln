// The body may not change what it walks, as with a Vec.
#include <stdlib::vec>
trait AsSlice<T> { asSlice &self -> [T]; }
struct Bag { items: Vec<long> }
methods Bag for AsSlice<long> {
    asSlice &self -> [long] { unsafe { return self.items.buf.ptr[..self.items.count]; } }
}
main -> long {
    b: Bag = Bag { };
    b.items.push(1);
    for x in b { b.items.push(x); }
    return 0;
}
