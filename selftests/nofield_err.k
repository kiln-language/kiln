// An unknown field used to reach the lowerer, which answered offset 0 -- the FIRST field -- and
// printed a debug line to stderr. The read came back as some other member's value.
struct P { a: long, b: long }
main -> int { p: P = P { a: 11, b: 22 }; return p.nosuch as int; }
