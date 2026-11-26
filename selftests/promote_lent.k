#include <stdlib::{thread, heap}>

// A local whose address is lent only to calls that keep no pointer to it lives in a register
// between those calls, its slot holding it only across them (`Flow.promoteLent`). The callee
// writes through what it is lent, so the value after each call is the callee's; a narrow local is
// copied at its own width. Where the callee keeps the pointer, passes it on to one that does, or
// hands it to another thread, or the caller holds a `recover`, the local stays in its slot, and
// what is written through the pointer later or from elsewhere is what the caller reads.
// `promote_lent_recover.k` has the `recover` case: a function holding one keeps all its locals in
// memory, and a `main` that copied it in would test nothing else here.

var gKept: long = 0;
var gSpin: long = 0;

// Each holds a loop, `advance` a long one, so each stays a call.
advance inout x:long n:long -> long {
    s: long = 0;
    for i in 0..n {
        s = s + i;
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (s << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (s >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    x = x + n;
    return s;
}
nudge inout b:u8 -> void {
    for i in 0..2 { gSpin = gSpin + i; }
    b = b + 200;
}
peek inout x:long -> long {
    s: long = 0;
    for i in 0..3 { s = s + x + i; }
    return s;
}

// The counter lent each turn, read and written around the calls.
walk n:long -> long {
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    p: long = 0;
    total: long = 0;
    while (p < n) {
        total = total + advance(&p, 3);
        total = total + p * 7;
        if ((total & 1) == 0) { p = p + 1; }
    }
    return total * 1000 + p;
}

// A `u8` wraps at its width across the call: 100 + 200 + 200 is 244 as a `u8`.
narrow -> long {
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    b: u8 = 100;
    nudge(&b);
    nudge(&b);
    return b as long;
}

// Lent to a callee that only reads it, then changed: the next call sees the change.
readOnly -> long {
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    v: long = 4;
    a: long = peek(&v);
    v = v * 10;
    return a * 1000 + peek(&v);
}

// Keeps the address it is lent: the parameter escapes. Each is long enough, and called from
// enough places, to stay a call.
unsafe keep inout x:long -> void {
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    gKept = (&x as *long) as long;
}
unsafe passOn inout x:long -> void {
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    keep(&x);
}
// Hands the address it is lent to another thread, and returns while that thread may still write it.
unsafe launch inout x:long -> Thread {
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    return spawn(&bumpThread, (&x as *long) as long);
}

// Written through the kept pointer after the call: the caller's variable is that slot.
viaKept -> long {
    v: long = 5;
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    unsafe {
        keep(&v);
        q: *long = gKept as *long;
        q[0] = 77;
    }
    return v;
}
viaPassOn -> long {
    v: long = 6;
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    unsafe {
        passOn(&v);
        q: *long = gKept as *long;
        q[0] = 88;
    }
    return v;
}

// Handed to another thread, which writes it before the join.
bumpThread ctrl:long -> void {
    unsafe {
        p: *long = threadArg(ctrl) as *long;
        p[0] = p[0] + 100;
    }
}
viaThread -> long {
    v: long = 3;
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    unsafe {
        t: Thread = spawn(&bumpThread, (&v as *long) as long);
        t.join();
    }
    return v;
}
// Handed on by a callee to another thread, which writes it after the callee has returned.
viaLaunch -> long {
    v: long = 3;
    for i in 0..3 {
        gSpin = gSpin ^ i;
        gSpin = gSpin + (i * 3) % 7;
        gSpin = gSpin ^ (gSpin << 2);
        gSpin = gSpin - (i * 5) % 11;
        gSpin = gSpin ^ (gSpin >> 1);
        gSpin = gSpin + (gSpin % 13);
    }
    unsafe {
        t: Thread = launch(&v);
        t.join();
    }
    return v;
}

main -> int {
    if (walk(20) != 400020 || walk(20) != 400020) { return 1; }
    if (narrow() != 244 || narrow() != 244) { return 2; }
    if (readOnly() != 15123 || readOnly() != 15123) { return 3; }
    if (viaKept() != 77 || viaKept() != 77) { return 4; }
    if (viaPassOn() != 88 || viaPassOn() != 88) { return 5; }
    if (viaThread() != 103 || viaThread() != 103) { return 6; }
    // Second callers, so `advance`, `passOn` and `launch` are not copied into their one call site.
    q: long = 1;
    advance(&q, 2);
    if (q != 3) { return 8; }
    if (viaLaunch() != 103 || viaLaunch() != 103) { return 9; }
    unsafe {
        passOn(&q);
        t: Thread = launch(&q);
        t.join();
    }
    if (q != 103) { return 10; }
    return 0;
}
