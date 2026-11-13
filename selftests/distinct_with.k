// `type T = distinct B with Add, Sub, ...`: the base's operators for T, opted into by trait, each
// written as the base's operation between the two values (and inlined to it). Without `with` a
// distinct type still has none (selftest distinct_op_err).
#include <stdlib::{core, cmp}>
type Meters = distinct long with Add, Sub, Mul, Div, Rem, Eq, Ord, Hash;
type Mask = distinct u8 with BitAnd, BitOr, BitXor, Shl, Shr, Not, Eq;
maxOf<T: Ord> a:T b:T -> T { if (a.cmp(b) < 0) { return b; } return a; }
main -> int {
    a: Meters = 30 as Meters;
    b: Meters = 12 as Meters;
    c: Meters = (a + b) * (2 as Meters) - (a / (3 as Meters)) % (4 as Meters);   // 84 - 2 = 82
    c += 1 as Meters;                                                            // 83
    if (a == b || !(a != b) || a < b || !(a >= b)) { return 1; }
    if (maxOf(a, b) != a) { return 2; }
    if (a.hash() != (30 as long).hash()) { return 3; }
    m: Mask = (12 as u8) as Mask;
    n: Mask = ((m | ((1 as u8) as Mask)) ^ ((4 as u8) as Mask)) & ~((128 as u8) as Mask);   // 9
    s: Mask = (n << ((1 as u8) as Mask)) >> ((1 as u8) as Mask);                            // 9
    if (s != n) { return 4; }
    return ((c as long) + (n as long)) as int;     // 92
}
