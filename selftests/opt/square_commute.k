// A result takes over the register of the operand that dies where it is made, the right one too
// where the two may be swapped (`RegAlloc.takeOperandReg`): `b = a ^ (a >> 7)` is `xor t, a`
// with no copy of `a` first, and a square is `imul r, r` in the register the value had.
// asm-lacks: square_commute::sq imul rax
// asm-count: square_commute::mix xor 1
var gK: long = 3;
sq x:long y:long -> long {
    a: long = x * gK + y;
    b: long = x + y * gK;
    return a * a + b * b + 1;
}
mix x:long -> long {
    a: long = x * gK;
    return (a ^ (a >> 7)) + a;
}
main -> int {
    f: fn(long, long) -> long = &sq;
    g: fn(long) -> long = &mix;
    if (f(2, 5) != 11 * 11 + 17 * 17 + 1) { return 1; }
    if (g(1000) != ((3000 ^ (3000 >> 7)) + 3000)) { return 2; }
    return 0;
}
