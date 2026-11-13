// Behind a trait object the receiver's type is erased, so a second operand OF that type cannot
// be named.
trait Ord2 { cmp &self other:Self -> int; }
struct P { v: long }
methods P for Ord2 { cmp &self other:P -> int { return (self.v - other.v) as int; } }
main -> int { p: P = P { v: 1 }; o: Ord2 = p; return 0; }
