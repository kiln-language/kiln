// `&x` on a struct is a LEND, and every `&` types as a plain `long`, so storing one in an
// integer read as `long = long` and laundered the borrow into an address that outlives it.
struct P { n: long }
main -> int { p: P = P { n: 7 }; a: long = &p; return a as int; }
