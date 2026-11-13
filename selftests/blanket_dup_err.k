// A blanket implementation is the written-out one for each type, so another for one of them is
// the duplicate it would be beside those.
pub trait Twice { twice &self -> long; }
methods<T: Integer> T for Twice { twice &self -> long { return (self as long) * 2; } }
methods long for Twice { twice &self -> long { return self * 2; } }
main -> int { return 0; }
