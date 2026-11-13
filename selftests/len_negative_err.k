// A length is never negative: `Buf<-4>` is refused where it is written.
struct Buf<N: long> { bytes: [u8; N] }
main -> int {
    b: Buf<-4>;
    return 0;
}
