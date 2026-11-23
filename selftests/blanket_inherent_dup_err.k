// An inherent blanket's method for `long` beside a hand-written one of the same name is the
// duplicate it would be written out.
methods<T: Integer> T { twice &self -> long { return (self as long) * 2; } }
methods long { twice &self -> long { return self * 2; } }
main -> int { x: long = 2; return x.twice() as int; }
