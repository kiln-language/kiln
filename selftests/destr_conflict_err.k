// A name the code after it writes through is a borrow of its element, so that code may not also
// replace the tuple: the borrow would point into an element that is gone.
struct P { x: long, y: long }
struct H { pair: (long, P) }
methods H { swap &self -> void { a, b = self.pair; b.x = 1; self.pair = (0, P { x: 2, y: 2 }); b.y = 3; } }
main -> int { h: H = H { pair: (1, P { x: 1, y: 2 }) }; h.swap(); return 0; }
