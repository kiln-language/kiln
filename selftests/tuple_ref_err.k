// A tuple is a value: a borrow cannot be one of its elements.
struct P { x: long }
f p:P -> (&P, long) { return (p, 1); }
main -> int { return 0; }
