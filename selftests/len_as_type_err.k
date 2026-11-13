// A length parameter stands where a length or a value goes, never where a type does.
struct Buf<N: long> { bytes: [u8; N] }
methods Buf<N> {
    first &self -> long { x: N = 0; return x; }
}
main -> int { return 0; }
