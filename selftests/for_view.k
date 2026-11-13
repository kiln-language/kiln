// `for x in xs` over any type implementing the core trait `AsSlice<T>`: walked as the slice its
// `asSlice` views (declared here, as `stdlib::core` will declare it). A scalar element is copied,
// a struct element borrowed in place, `for x in &xs` writes through it.
#include <stdlib::vec>
trait AsSlice<T> { asSlice &self -> [T]; }

struct Bag { items: Vec<long> }
methods Bag for AsSlice<long> {
    asSlice &self -> [long] { unsafe { return self.items.buf.ptr[..self.items.count]; } }
}
struct Pt { x: long, y: long }
struct Wrap<T> { inner: Vec<T> }
methods Wrap<T> for AsSlice<T> {
    asSlice &self -> [T] { unsafe { return self.inner.buf.ptr[..self.inner.count]; } }
}
total b:Bag -> long { s: long = 0; for x in b { s = s + x; } return s; }
main -> long {
    b: Bag = Bag { };
    for i in 1..5 { b.items.push(i); }             // 1 + 2 + 3 + 4 = 10
    w: Wrap<Pt> = Wrap<Pt> { };
    w.inner.push(Pt { x: 1, y: 2 });
    w.inner.push(Pt { x: 3, y: 4 });
    for p in &w { p.y = p.y * 2; }                  // writes each element in place
    s: long = 0;
    for p in w { s = s + p.x + p.y; }               // 1 + 4 + 3 + 8 = 16
    e: Wrap<long> = Wrap<long> { };
    for x in e { s = s + 100; }                      // empty: no turn
    return total(b) + s + 16;                        // 10 + 16 + 16 = 42
}
