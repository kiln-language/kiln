// `!` on a struct is refused outright. Unlike `~` it gets no trait: it asks whether a truth value
// is false, and a block of bytes has none to ask about.
struct Z { q: long }
main -> int { a: Z = Z { q: 1 }; if (!a) { return 1; } return 0; }
