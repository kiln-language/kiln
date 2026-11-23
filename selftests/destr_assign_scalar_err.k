// The same for an element that is a scalar, which could only ever be assigned as a whole.
struct P { x: long, y: long }
bump inout t:(long, P) -> void { n, p = t; n = n + 1; }
main -> int { t: (long, P) = (1, P { x: 1, y: 2 }); bump(&t); return 0; }
