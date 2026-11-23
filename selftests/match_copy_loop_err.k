// A struct element of `for e in xs` is a read-only borrow, and so is a binding of its payload
// that the arm writes through.
#include <stdlib::vec>
struct P { x: long, y: long }
enum E { Num(long), Pt(P) }
main -> int {
    v: Vec<E>;
    v.push(E.Pt(P { x: 1, y: 2 }));
    for e in v { match e { Pt(p) { p.x = 5; } _ { } } }
    return 0;
}
