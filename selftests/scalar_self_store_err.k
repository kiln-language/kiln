// `self = v` in a `&self` method of a scalar would change only the method's own copy.
trait Reset { reset &self -> void; }
methods long for Reset { reset &self -> void { self = 0; } }
main -> int { x: long = 3; x.reset(); return x as int; }
