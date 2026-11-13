// Multiplying a struct with no `Mul` is refused, rather than multiplying the addresses the two
// operands flow as. `+` was always refused this way; the other four were not.
struct V { x: long }

main -> int {
    a: V = V { x: 10 };
    b: V = V { x: 3 };
    c: V = a * b;
    return c.x as int;
}
