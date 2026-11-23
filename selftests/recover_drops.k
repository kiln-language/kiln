#include <stdlib::{io, recover}>

// What the body of a `recover` owns when a `raise` arrives is released once, before the handler
// runs: a local still holding its value is, and one moved away (into the callee that raised, or
// into a value released already) is not.

var gDrops: long = 0;
struct Res { id: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.id; } }

fail -> never { unsafe { raise(); } }
consume sink r:Res -> void { if (r.id > 0) { fail(); } }
take sink r:Res -> long { return r.id; }
keep r:Res -> long { return r.id; }

main -> long {
    unsafe {
        recover {
            a: Res = Res { id: 1 };
            b: Res = Res { id: 10 };
            fail();
        } else { }
    }
    if (gDrops != 11) { return 1; }

    // Moved into the callee that raised: the callee owned it, so nothing here releases it.
    gDrops = 0;
    unsafe {
        recover {
            c: Res = Res { id: 100 };
            consume(c);
        } else { }
    }
    if (gDrops != 0) { return 2; }

    // Released at the end of an inner scope, then a raise: not released again.
    gDrops = 0;
    unsafe {
        recover {
            {
                d: Res = Res { id: 1000 };
                keep(d);
            }
            e: Res = Res { id: 2 };
            fail();
        } else { }
    }
    if (gDrops != 1002) { return 3; }

    // A body that ends normally: each local released once, at its end.
    gDrops = 0;
    unsafe {
        recover {
            f: Res = Res { id: 5 };
        } else { gDrops = 77; }
    }
    if (gDrops != 5) { return 4; }

    // A raise inside a handler goes outward: the inner body's local is released once, as the
    // inner handler begins, and not again by the outer one.
    gDrops = 0;
    unsafe {
        recover {
            recover {
                g: Res = Res { id: 20 };
                fail();
            } else {
                fail();
            }
        } else { }
    }
    if (gDrops != 20) { return 5; }

    // Declared before the statement and moved in the body: possibly moved in the handler, and
    // released at the end of its scope as its flag says. `take` released it, so that is all.
    gDrops = 0;
    {
        h: Res = Res { id: 300 };
        unsafe {
            recover {
                take(h);
                fail();
            } else { }
        }
    }
    if (gDrops != 300) { return 6; }
    return 0;
}
