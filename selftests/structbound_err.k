// A bound on the TYPE's own parameter holds for every instance, unlike a methods block's, which
// is conditional. The header's bounds used to be parsed and discarded.
struct Plain { id: int }
struct Wrap<W: Default> { inner: W, n: int }
g: Wrap<Plain>;
main -> int { return 0; }
