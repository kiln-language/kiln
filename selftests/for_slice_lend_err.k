// A slice is a read-only view unless it is an `inout` parameter, and `for p in &xs` writes through it.
struct P { x: long }
clear xs:[P] -> void { for p in &xs { p.x = 0; } }
main -> int { a: [P; 1]; a[0] = P { x: 1 }; clear(a[..]); return 0; }
