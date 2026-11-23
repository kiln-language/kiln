#include <stdlib::{io, recover}>

// A `raise` several calls below a `recover` body lands in its handler. A local the body wrote
// before the call that raised holds what it wrote, and the write after that call never happened.
// A `recover` whose body ends normally unlinks its record, so a later `raise` goes to the record
// further out.

var gSteps: long = 0;

down n:long -> long {
    gSteps = gSteps + 1;
    if (n == 0) { unsafe { raise(); } }
    return down(n - 1) + 1;
}

struct Box1 { v: long }
var gVal: long = 0;

// A store the handler reads, then a call that raises, then another store: only the first lands.
// Nothing in this function knows a handler is waiting.
storeAround inout x:Box1 -> void {
    x.v = 1;
    down(3);
    x.v = 2;
}

// The same through a global.
globalAround -> void {
    gVal = 1;
    down(3);
    gVal = 2;
}

main -> long {
    x: long = 0;
    reached: long = 0;
    unsafe {
        recover {
            x = 1;
            down(5);
            x = 2;
        } else {
            reached = 1;
        }
    }
    if (reached != 1 || x != 1 || gSteps != 6) { return 1; }
    if (recoverArmed()) { return 2; }

    // A body that does not raise: the handler does not run, and the record is gone afterwards.
    y: long = 0;
    unsafe {
        recover { y = 5; } else { y = 9; }
    }
    if (y != 5 || recoverArmed()) { return 3; }

    // The outer record is the one a later `raise` finds, not the inner one that ended.
    which: long = 0;
    unsafe {
        recover {
            recover { which = 1; } else { which = 2; }
            down(2);
        } else {
            which = which + 10;
        }
    }
    if (which != 11) { return 4; }

    // Through a struct a callee writes, then raises.
    b: Box1 = Box1 { v: 0 };
    unsafe {
        recover { storeAround(&b); } else { b.v = b.v + 100; }
    }
    if (b.v != 101) { return 5; }
    unsafe {
        recover { globalAround(); } else { gVal = gVal + 100; }
    }
    if (gVal != 101) { return 6; }
    return 0;
}
