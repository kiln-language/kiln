// Each length is its own type: a `Buf<8>` is not a `Buf<16>`, and assigning one to the other is
// refused rather than copying 16 bytes out of 8.
struct Buf<N: long> { bytes: [u8; N], used: long }
main -> int {
    a: Buf<8> = Buf { used: 1 };
    b: Buf<16> = a;
    return b.used as int;
}
