// A trait object is a data pointer and a vtable, reached only through the trait's methods.
trait Shape { area &self -> long; }
struct Sq { s: long }
methods Sq for Shape { area &self -> long { return self.s * self.s; } }
peek sh:Shape -> long { return sh.data; }
main -> int { q: Sq = Sq { s: 3 }; return peek(q) as int; }
