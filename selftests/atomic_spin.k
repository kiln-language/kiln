// Atomics between threads. A loop waiting on a flag another thread clears reads it on every trip,
// and a plain read after the wait sees what the other thread wrote before clearing it: the
// acquire load is where facts about shared memory end, so neither is kept from before it. Two
// threads adding at once lose no update.
#include <stdlib::{io, thread, heap}>
pub unsafe builtin atomicLoad p:*long -> long;
pub unsafe builtin atomicStore p:*long v:long -> void;
pub unsafe builtin atomicAdd p:*long delta:long -> long;

var gFlag: long = 1;
var gCount: long = 0;

// Sets the word after the flag, then clears the flag with a release store. A thread body is handed
// its control block; what `spawn` was given is `threadArg` of it.
publish ctrl:long -> void {
    sleepMs(20);
    unsafe {
        p: *long = threadArg(ctrl) as *long;
        p[1] = 42;
        atomicStore(p, 0);
    }
}
raiseFlag ctx:long -> void {
    sleepMs(20);
    unsafe { atomicStore(&gFlag as *long, 0); }
}
adder ctx:long -> void {
    unsafe { for i in 0..100000 { atomicAdd(&gCount as *long, 1); } }
}

// The word after the flag, read before and after the wait: the second read is its own.
waitPtr at:long -> long {
    unsafe {
        p: *long = at as *long;
        before: long = p[1];
        while (atomicLoad(p) != 0) { }
        return before * 1000 + p[1];
    }
}
waitGlobal -> long {
    n: long = 0;
    unsafe { while (atomicLoad(&gFlag as *long) != 0) { n = n + 1; } }
    return n;
}

main -> int {
    at: long = malloc(16);
    unsafe { p: *long = at as *long; p[0] = 1; p[1] = 0; }
    t: Thread = spawn(&publish, at);
    got: long = waitPtr(at);
    t.join();
    if (got % 1000 != 42) { return 1; }
    u: Thread = spawn(&raiseFlag, 0);
    waitGlobal();
    u.join();
    a: Thread = spawn(&adder, 0);
    b: Thread = spawn(&adder, 0);
    a.join();
    b.join();
    if (gCount != 200000) { return 2; }
    println("atomic_spin");
    return 0;
}
