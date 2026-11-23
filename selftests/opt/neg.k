// `0 - x` and `~x + 1` are negations (`Flow.identity` makes each a product by -1, which the
// emitter writes as `neg`): no zeroed register and `sub`, no `not` and `add`.
// asm-has: neg::lowest neg
// asm-lacks: neg::lowest not
// asm-has: neg::minus neg
// asm-lacks: neg::minus sub
var gA: long = 12;
lowest z:long -> long { return z & (~z + 1); }
minus z:long -> long { return 0 - z; }
// A product by another negative constant stays a product.
times z:long -> long { return z * (0 - 3); }
// `~x + 1` where `x` changes between the two: the old `x`, negated, not the new one.
twist n:long -> long {
    x: long = n;
    s: long = 0;
    for i in 0..3 {
        t: long = ~x;
        x = x * 3 + i;
        s = s + (t + 1);
    }
    return s + x;
}
main -> int {
    p: fn(long) -> long = &lowest;
    q: fn(long) -> long = &minus;
    if (p(gA) != 4 || q(gA) != -12) { return 1; }
    if (p(0) != 0 || q(0) != 0) { return 2; }
    if (p(-8) != 8 || q(-8) != 8) { return 3; }
    r: fn(long) -> long = &twist;
    if (r(2) != 32) { return 4; }
    m: fn(long) -> long = &times;
    if (m(7) != -21) { return 5; }
    return 0;
}
