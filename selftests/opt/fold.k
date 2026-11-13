// Constants fold at the operation's width, branches on them go, a multiply by a power of two is
// a shift, and an immutable global's known value replaces the read of it.
// ir-has: fold::f const 42
// ir-lacks: fold::f mul
// ir-has: fold::g const -128
// ir-lacks: fold::h jcc
// ir-has: fold::k shl
// ir-has: fold::glob const 4096
LIMIT: long = 4096;
f -> long { x: long = 6; y: long = x * 7; return y; }
g -> long { b: i16 = 127; c: i16 = b + 1; d: char = c as char; return d as long; }
h x:long -> long { k: long = 3; if (k > 2) { return x + 1; } return x - 1; }
k x:long -> long { return x * 8; }
glob -> long { return LIMIT; }
main -> int {
    if (f() != 42 || g() != -128 || h(1) != 2 || k(5) != 40 || glob() != 4096) { return 1; }
    return 0;
}
