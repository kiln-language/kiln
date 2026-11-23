// Values live across calls to a function that leaves most registers alone stay in caller-saved
// registers it does not change (`RegAlloc.siteMask`): `keeper` saves no callee-saved register
// for them and writes nothing to the frame, where without the callee's set each of the three
// would take one of r12 to r14. `sharer` makes the same calls through a fn value, whose callee
// may change anything, so its values go to callee-saved registers.
// asm-lacks: ipra_keep::keeper push r12
// asm-lacks: ipra_keep::keeper [rbp
// asm-has: ipra_keep::sharer push r12
var gN: long = 0;
// A loop: never copied into its callers.
leaf x:long -> long {
    s: long = x;
    for i in 0..(x & 1) + 1 { s = s + i; }
    return s;
}
keeper a:long b:long c:long -> long {
    r: long = leaf(a);
    r = r + leaf(b) * c;
    r = r + leaf(c) + a + b;
    return r + a * b * c;
}
sharer f:fn(long) -> long a:long b:long c:long -> long {
    r: long = f(a);
    r = r + f(b) * c;
    r = r + f(c) + a + b;
    return r + a * b * c;
}
main -> int {
    // Through a fn value, so `keeper` is its own function and not copied into `main`.
    k: fn(long, long, long) -> long = &keeper;
    if (k(1, 2, 3) != 21) { return 1; }
    s: fn(fn(long) -> long, long, long, long) -> long = &sharer;
    if (s(&leaf, 1, 2, 3) != 21) { return 2; }
    return 0;
}
