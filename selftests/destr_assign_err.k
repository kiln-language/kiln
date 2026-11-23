// A name a destructure through a borrow binds is the element where it lies: it cannot be given
// another value as a whole. Assign the element itself, or replace the whole tuple.
struct P { x: long, y: long }
struct H { pair: (long, P) }
methods H { reset &self -> void { a, b = self.pair; b = P { x: 0, y: 0 }; } }
main -> int { h: H = H { pair: (1, P { x: 1, y: 2 }) }; h.reset(); return 0; }
