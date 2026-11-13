// A truth value prints as `true`/`false` whatever made it: a `bool`, but also `!x`, a comparison,
// `&&` and `||`, which the checker types as an `int` 0 or 1. At run time (`Lowerer.boxAny`) and at
// compile time (the evaluator's box, a folded global).
#include <stdlib::{io, string}>

shown a:long t:bool -> String {
    return format("{} {} {} {} {} {}", t, !t, a < 4, a == 4 && t, !(a > 9) || false, a != 3);
}

FOLDED: long = check(3, true);

check a:long t:bool -> long {
    if (!shown(a, t).eq("true false true false true false")) { return 1; }
    if (!format("{}", !t).eq("false")) { return 2; }
    return 0;
}

main -> long {
    if (FOLDED != 0) { return 10 + FOLDED; }
    t: bool = true;
    r: long = check(3, t);
    if (r != 0) { return 20 + r; }
    println("{} {}", !t, 2 > 1);
    return 0;
}
