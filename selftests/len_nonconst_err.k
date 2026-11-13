// A length has to be a compile-time constant. A `var` global can be written at runtime, so its
// value is not fixed, and `Buf<SIZE>` cannot name one instance.
var SIZE: long = 8;
struct Buf<N: long> { bytes: [u8; N] }
main -> int {
    b: Buf<SIZE>;
    return 0;
}
