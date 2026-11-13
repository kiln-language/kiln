// An instance a template's bound refuses is reported where it was asked for.
struct Plain { id: int }
struct Wrap<W: Default> { inner: W }
helper -> int { return 1; }
main -> int {
    x: int = helper();
    g: Wrap<Plain>;
    return x;
}
