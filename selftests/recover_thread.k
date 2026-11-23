#include <stdlib::{io, recover, thread}>

// The chain of armed `recover`s is per thread: a spawned thread raises into its own handler, and
// the main thread's record, armed the whole time, is untouched by it.

var gResult: long = 0;

deep n:long -> void {
    if (n == 0) { unsafe { raise(); } }
    deep(n - 1);
}

worker ctrl:long -> void {
    r: long = 0;
    unsafe {
        recover {
            r = 1;
            deep(10);
            r = 2;
        } else {
            r = r + 40;
        }
    }
    if (recoverArmed()) { r = 99; }
    gResult = r;
}

main -> long {
    status: long = 0;
    unsafe {
        recover {
            t: Thread = spawn(&worker, 0);
            t.join();
            if (!recoverArmed()) { status = 1; }
            deep(3);
            status = 2;
        } else {
            status = status + 10;
        }
    }
    if (status != 10) { return 1; }
    if (gResult != 41) { return 2; }
    return 0;
}
