// A compare and branch the optimizer's first run leaves with a constant on each side is decided at
// the end of that run (`Opt.foldConstBranches`, `constCompare`), the way the comparison's kind
// says: unsigned above the sign bit, signed below zero, at the kind's width.
// ir-lacks: refold_compare::bigU jcc
// ir-lacks: refold_compare::negI jcc
// ir-lacks: refold_compare::byteU jcc
local bigU -> long {
    a: u64 = 9223372036854775808;
    b: u64 = 1;
    if (a > b) { return 1; }
    return 2;
}
local negI -> long {
    a: i8 = -5;
    b: i8 = 3;
    if (a < b) { return 1; }
    return 2;
}
local byteU -> long {
    a: u8 = 200;
    b: u8 = 100;
    if (a >= b) { return 1; }
    return 2;
}
main -> int {
    f: fn() -> long = &bigU;
    g: fn() -> long = &negI;
    h: fn() -> long = &byteU;
    if (f() != 1) { return 1; }
    if (g() != 1) { return 2; }
    if (h() != 1) { return 3; }
    return 0;
}
