#include <stdlib::{io, recover}>

// Nested `recover`s: a `raise` goes to the innermost armed one, and one inside a handler goes to
// the next one out, since the handler runs with its own record unlinked. Leaving a body by
// `return`, `break` or `continue` unlinks its record, so a later `raise` goes further out.

fail -> never { unsafe { raise(); } }

var gLog: long = 0;
note d:long -> void { gLog = gLog * 10 + d; }

innerThenOuter -> long {
    unsafe {
        recover {
            recover {
                note(1);
                fail();
            } else {
                note(2);
                fail();
            }
        } else {
            note(3);
        }
    }
    return gLog;
}

// `return` out of a body: the caller's `raise` afterwards goes to the caller's own record.
early -> long {
    unsafe {
        recover {
            return 7;
        } else {
            return 8;
        }
    }
    return 9;
}

loops -> long {
    n: long = 0;
    for i in 0..5 {
        unsafe {
            recover {
                if (i == 1) { continue; }
                if (i == 3) { break; }
                n = n + 10;
                if (i == 2) { fail(); }
            } else {
                n = n + 1;
            }
        }
    }
    return n;
}

main -> long {
    if (innerThenOuter() != 123) { return 1; }
    out: long = 0;
    unsafe {
        recover {
            if (early() != 7) { out = 50; }
            fail();
        } else {
            out = out + 1;
        }
    }
    if (out != 1) { return 2; }
    caught: long = 0;
    unsafe {
        recover {
            // i = 0 adds 10, i = 1 goes on, i = 2 adds 10 and raises (1 more), i = 3 leaves
            if (loops() != 21) { caught = 100; }
            fail();
        } else {
            caught = caught + 1;
        }
    }
    if (caught != 1) { return 3; }
    if (recoverArmed()) { return 4; }
    return 0;
}
