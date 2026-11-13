// `~` on a struct with no `Not` is refused rather than complementing its address.
struct Z { q: long }
main -> int { a: Z = Z { q: 1 }; b: Z = ~a; return b.q as int; }
