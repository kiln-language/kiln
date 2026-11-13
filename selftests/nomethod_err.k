// No method of that name anywhere. The call used to be emitted and NASM reported the mangled
// symbol from a line number in generated assembly.
struct P { a: long }
main -> int { p: P = P { a: 1 }; p.nomethod(); return 0; }
