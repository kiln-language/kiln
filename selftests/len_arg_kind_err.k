// An argument is the kind of thing its parameter is: `Buf<long>` gives a type where Buf's N is
// a length.
struct Buf<N: long> { bytes: [u8; N] }
main -> int {
    b: Buf<long>;
    return 0;
}
