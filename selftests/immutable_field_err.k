// An assignment to a field of an immutable global is refused.
struct P { a: long, b: long }
ORIGIN: P = P { a: 0, b: 0 };
main -> int { ORIGIN.a = 1; return 0; }
