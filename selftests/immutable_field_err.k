// An assignment through an immutable global -- a field of it -- is refused.
struct P { a: long, b: long }
ORIGIN: P = P { a: 0, b: 0 };
main -> int { ORIGIN.a = 1; return 0; }
