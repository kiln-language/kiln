// `p.x()` where `x` is a field: refused at the call, with the hint. (`len()` reads a `len` field:
// selftest len_call.)
struct P { x: long }
main -> int { p: P = P { x: 3 }; return p.x() as int; }
