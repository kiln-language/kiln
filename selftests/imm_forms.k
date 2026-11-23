// `asm.k` `movImm`: a constant goes into a register as `mov r32, v` for 0..2^32-1 (which
// zero-extends), as the sign-extended `mov r64, dword v` for -2^31..-1, and with all eight bytes
// only past both. Each value at and around those edges comes out of a function that returns it as
// a constant, and is checked against the same value computed at run time from shifts the
// optimizer cannot see through.

#include <stdlib::vec>

var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }

// Called from two places through a value, so its constants are materialized here, not folded.
pick k:long -> long {
    if (k == 0) { return 0; }
    if (k == 1) { return 1; }
    if (k == 2) { return 2147483647; }
    if (k == 3) { return 2147483648; }
    if (k == 4) { return 4294967295; }
    if (k == 5) { return 4294967296; }
    if (k == 6) { return -1; }
    if (k == 7) { return -2147483648; }
    if (k == 8) { return -2147483649; }
    if (k == 9) { return 9223372036854775807; }
    if (k == 10) { return 0 - 9223372036854775807 - 1; }
    if (k == 11) { return -4294967296; }
    return 77;
}

main -> int {
    f: fn(long) -> long = &pick;
    one: long = dyn(1);
    p31: long = one << dyn(31);
    p32: long = one << dyn(32);
    p63: long = one << dyn(63);
    want: Vec<long> = vec![0, 1, p31 - 1, p31, p32 - 1, p32, 0 - one, 0 - p31, 0 - p31 - 1, p63 - 1, p63, 0 - p32];
    bad: long = 0;
    for k in 0..12 {
        if (f(dyn(k)) != want[k]) { bad = bad | (1 << k); }
    }
    if (pick(dyn(12)) != 77) { bad = bad | 4096; }
    return (bad != 0) as int;
}
