// Ordering a struct that implements no `Ord` is refused, rather than compiling to a comparison of
// the addresses the two operands happen to flow as. `==` has always been refused this way; `<` was
// not, and answered from the frame layout instead.
struct V { x: long }

main -> int {
    a: V = V { x: 1 };
    b: V = V { x: 2 };
    if (a < b) { return 1; }
    return 0;
}
