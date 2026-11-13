// Only a tuple is destructured.
struct P { x: long, y: long }
mk -> P { return P { x: 1, y: 2 }; }
main -> int { a, b = mk(); return 0; }
