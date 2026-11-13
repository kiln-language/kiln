// A global aggregate holding floats is folded and placed in the binary like any other: a
// struct's f64 and f32 fields, an array of f64, a tuple, an enum's f64 payload, a Vec<f64>'s heap
// block (built by `vecOf`: `vec!` cannot carry a float literal until stdlib::ast has `Float`), and
// a `var` one (in `.data`, still written at run time).
#include <stdlib::vec>
struct S { x: f64, n: long, h: f32 }
enum Shape { Circle(f64), Square(f64, f64), Empty }
G: S = S { x: 1.5, n: 2, h: 0.25 };
ARR: [f64; 3] = [0.5, 1.5, 2.5];
T: (f64, long) = (3.25, 4);
SH: Shape = Shape.Square(2.0, 0.75);
V: Vec<f64> = vecOf(1.0, 2.0, 4.0);
var gS: S = S { x: -6.5, n: 1, h: 1.5 };
struct Wrap { inner: S, w: f32 }
W: Wrap = Wrap { inner: S { x: 9.0, n: 3, h: 2.5 }, w: 1.25 };
FS: [f32; 2] = [0.5, 1.25];
main -> long {
    if (G.x != 1.5 || G.n != 2 || G.h != 0.25) { return 1; }
    s: f64 = 0.0;
    for x in ARR { s = s + x; }
    if (s != 4.5) { return 2; }
    if (T.0 != 3.25 || T.1 != 4) { return 3; }
    match SH { Square(a, b) { if (a * b != 1.5) { return 4; } } _ { return 5; } }
    if (V.get(0) + V.get(1) + V.get(2) != 7.0) { return 6; }
    gS.x = gS.x * 2.0;
    if (gS.x != -13.0 || gS.h != 1.5) { return 7; }
    if (W.inner.x != 9.0 || W.w != 1.25 || FS[1] != 1.25 || W.inner.h != 2.5) { return 8; }
    return 42;
}
