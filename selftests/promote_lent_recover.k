#include <stdlib::recover>

// A local lent to a callee that writes it and then raises, inside the caller's `recover`: the
// handler sees the value the callee wrote. During the call the slot is the variable, and a
// function holding a `recover` keeps its locals in memory (`Flow.promoteLent`).

var gSpin: long = 0;

unsafe writeThenRaise inout x:long -> void {
    for i in 0..2 { gSpin = gSpin + i; }
    x = 41;
    raise();
}
caught -> long {
    v: long = 1;
    unsafe {
        recover {
            writeThenRaise(&v);
            v = 0;
        } else {
            v = v + 1;
        }
    }
    return v;
}

main -> int {
    if (caught() != 42) { return 1; }
    return 0;
}
