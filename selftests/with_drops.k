// A `with` releases its guard exactly once on every way out of the block: the end, a `break`
// and a `continue` out of the loop around it, a `return`, a `?` that fails and one that does
// not, a `raise` that a `recover` around it catches, and each of two nested ones. The guard's
// `drop` counts, so a release run twice (or skipped) shows in the totals.
#include <stdlib::{core, recover, result}>

var gDrops: long = 0;
var gHolds: long = 0;
struct Cell { v: long }
struct Guard { n: long }
methods Guard for Drop { drop &self -> void { gDrops = gDrops + self.n; } }
methods Cell { hold &self -> Guard { gHolds = gHolds + 1; return Guard { n: self.v }; } }

// A guard that projects: inside the block, a read of the wrapper is a read through the guard.
struct Box { v: long }
struct View { n: long }
methods View for Drop { drop &self -> void { gDrops = gDrops + 100; } }
methods View { get &self -> long { return self.n; } set &self x:long -> void { self.n = x; } }
methods Box { hold &self -> View { gHolds = gHolds + 1; return View { n: self.v }; } }

fail -> never { unsafe { raise(); } }
half x:long -> Result<long, long> { if (x % 2 != 0) { return Result.Err(x); } return Result.Ok(x / 2); }
viaTry c:Cell x:long -> Result<long, long> {
    h: long = 0;
    with c { h = half(x)?; }
    return Result.Ok(h);
}
early c:Cell n:long -> long {
    with c { if (n > 0) { return n; } }
    return 0;
}
through b:Box -> long {
    with b { return b + 1; }
    return 0;
}
fresh -> void { gHolds = 0; gDrops = 0; }

main -> int {
    c: Cell = Cell { v: 1 };
    with c { gSeen(); }
    if (gHolds != 1 || gDrops != 1) { return 1; }

    fresh();
    for i in 0..3 { with c { if (i == 1) { break; } } }
    if (gHolds != 2 || gDrops != 2) { return 2; }

    fresh();
    for i in 0..3 { with c { if (i == 1) { continue; } gSeen(); } }
    if (gHolds != 3 || gDrops != 3) { return 3; }

    fresh();
    if (early(c, 5) != 5 || early(c, 0) != 0) { return 4; }
    if (gHolds != 2 || gDrops != 2) { return 5; }

    fresh();
    r: Result<long, long> = viaTry(c, 3);
    if (gHolds != 1 || gDrops != 1) { return 6; }
    fresh();
    r = viaTry(c, 4);
    if (gHolds != 1 || gDrops != 1) { return 7; }

    fresh();
    unsafe { recover { with c { fail(); } } else { } }
    if (gHolds != 1 || gDrops != 1) { return 8; }

    fresh();
    d: Cell = Cell { v: 10 };
    with c { with d { gSeen(); } }
    if (gHolds != 2 || gDrops != 11) { return 9; }

    fresh();
    b: Box = Box { v: 41 };
    if (through(b) != 42) { return 10; }
    if (gHolds != 1 || gDrops != 100) { return 11; }
    return 0;
}

var gSeenCount: long = 0;
gSeen -> void { gSeenCount = gSeenCount + 1; }
