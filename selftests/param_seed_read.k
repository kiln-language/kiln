#include <stdlib::{io}>

// A parameter whose address is taken (lent to an `inout` parameter, captured by a closure) lives
// in its slot, and a read of it that the optimizer sees holds the value the parameter arrived
// with reads the seed's temp instead, which the prologue then has to fill. Integers, a float, a
// narrow type through a generic, and the argument after another.

viaObj f:Fn() -> void -> void { f(); }
var gSeen: long = 0;
var gSeenF: f64 = 0.0;

keep v:long -> long { out: long = v; viaObj(|| { gSeen = gSeen + v; }); return out; }
bump inout p:long -> void { p = p + 1; }
keep2 v:long -> long { out: long = v; bump(&v); return out + v; }
second a:long v:long -> long { out: long = v; viaObj(|| { gSeen = gSeen + a + v; }); return out * 10 + a; }
keepF v:f64 -> f64 { out: f64 = v; viaObj(|| { gSeenF = gSeenF + v; }); return out; }
one<T: Copy> v:T -> T { out: T = v; viaObj(|| { out = v; }); return out; }

main -> int {
    if (keep(7) != 7 || gSeen != 7) { return 1; }
    if (keep2(10) != 21) { return 2; }
    if (second(3, 4) != 43 || gSeen != 14) { return 3; }
    if (keepF(2.5) != 2.5 || gSeenF != 2.5) { return 4; }
    if (one(5) != 5) { return 5; }
    m: int = -6;
    if (one(m) != -6) { return 6; }
    println("param_seed_read");
    return 0;
}
