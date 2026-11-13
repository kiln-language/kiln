// A type parameter is not a length: `[u8; T]` is refused, however T is bound.
struct Buf<T> { bytes: [u8; T] }
main -> int { return 0; }
