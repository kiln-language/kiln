// Only the compiler's categories of scalars may stand in a blanket implementation.
pub trait Twice { twice &self -> long; }
methods<T: Number> T for Twice { twice &self -> long { return (self as long) * 2; } }
main -> int { return 0; }
