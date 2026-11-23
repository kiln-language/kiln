// A borrowed parameter's bytes written through an address derived from it that went somewhere
// first: a slot of the frame, a global, a callee that keeps it. Read back from there the address
// has no known origin, and the write must still end what was known of the parameter. Each check
// reads a field, writes 5 into it that way and reads it again (1 + 5); the depth, read out of a
// `var` global, keeps the function out of `main`, where the value is a local and not a borrow.
// Exits with the number of the first check that fails.
#include <stdlib::{io}>

struct P { a: long, b: long }
struct Hold { q: *long, n: long }

var gDepth: long = 1;
var gAt: long = 0;

// Kept in a struct in the frame and written through the copy read back out of it.
inFrame inout p:P n:long -> long {
    if (n > 0) { return inFrame(&p, n - 1); }
    t: long = p.a;
    unsafe {
        h: Hold = Hold { q: &p.a, n: n };
        h.q[0] = 5;
    }
    return t + p.a;
}

// The same in a callee that is not copied into its caller (it holds a loop and has two callers):
// its summary must say it writes its parameter. `refresh` writes the slot's pointer back, so
// `poke` reads it out of its frame not knowing what it is.
refresh inout h:Hold k:long -> void {
    s: long = 0;
    for i in 0..k { s += i; }
    h.q = h.q;
    h.n = h.n + s - s;
}
poke inout p:P k:long -> void {
    s: long = 0;
    for i in 0..k { s += i; }
    unsafe {
        h: Hold = Hold { q: &p.a, n: s };
        refresh(&h, k);
        h.q[0] = 5 + h.n - s;
    }
}
inCallee inout p:P n:long -> long {
    if (n > 0) { return inCallee(&p, n - 1); }
    t: long = p.a;
    poke(&p, 2);
    return t + p.a;
}

// Kept in a global and written through what is read back out of it.
inGlobal inout p:P n:long -> long {
    if (n > 0) { return inGlobal(&p, n - 1); }
    t: long = p.a;
    unsafe { gAt = (&p.a) as long; }
    unsafe { q: *long = gAt as *long; q[0] = 5; }
    return t + p.a;
}

// Kept in a global by the caller and written through it by a callee it is not handed to.
pokeGlobal k:long -> void {
    s: long = 0;
    for i in 0..k { s += i; }
    unsafe { q: *long = gAt as *long; q[0] = 5 + s - s; }
}
throughGlobal inout p:P n:long -> long {
    if (n > 0) { return throughGlobal(&p, n - 1); }
    t: long = p.a;
    unsafe { gAt = (&p.a) as long; }
    pokeGlobal(3);
    return t + p.a;
}

main -> int {
    x: P = P { a: 1, b: 2 };
    r: long = inFrame(&x, gDepth);
    println("{}", r);
    if (r != 6) { return 1; }
    x.a = 1;
    r = inCallee(&x, gDepth);
    println("{}", r);
    if (r != 6) { return 2; }
    x.a = 1;
    r = inGlobal(&x, gDepth);
    println("{}", r);
    if (r != 6) { return 3; }
    x.a = 1;
    r = throughGlobal(&x, gDepth);
    println("{}", r);
    if (r != 6) { return 4; }
    x.a = 1;
    poke(&x, 1);
    pokeGlobal(1);
    h: Hold = Hold { q: 0 as *long, n: 0 };
    unsafe { h.q = &x.b; }
    refresh(&h, 1);
    return 0;
}
