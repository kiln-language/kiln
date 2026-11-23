// Loop-invariant code motion (`flow.k` `hoist`) moves out only what is the same on every trip.
// Each loop here reads something its own body (or a call, or a pointer) changes, or something
// that does not change, and the sums must come out as written. Exit 0 when all do.
#include <stdlib::vec>
struct Box { n: long, m: long }
var gHits: long = 0;
var gP: long = 0;

bump inout b:Box -> void { b.n = b.n + 1; gHits = gHits + 1; }
keep b:&Box -> long { return b.m; }

// A field the body stores to is read again each trip.
stored -> long {
    b: Box = Box { n: 1, m: 10 };
    s: long = 0;
    for i in 0..5 { s = s + b.n; b.n = b.n + 2; }
    return s;                              // 1 + 3 + 5 + 7 + 9
}
// A field a call writes, through its summary.
called -> long {
    b: Box = Box { n: 0, m: 7 };
    s: long = 0;
    for i in 0..4 { s = s + b.n * 10 + b.m; bump(&b); }
    return s;                              // (0+1+2+3)*10 + 4*7
}
// A field written through a raw pointer to it.
aliased -> long {
    b: Box = Box { n: 2, m: 0 };
    s: long = 0;
    unsafe {
        p: *long = &b.n as *long;
        for i in 0..3 { s = s + b.n; *p = *p * 3; }
    }
    return s;                              // 2 + 6 + 18
}
// What does not change: a field nothing writes, a sum of two values from before the loop, a
// borrow's field, a Vec's length and buffer; all hoisted, all still right.
invariant v:&Vec<long> a:long c:long -> long {
    b: Box = Box { n: 3, m: 4 };
    s: long = 0;
    for i in 0..v.len() { s = s + v[i] * (a + c) + b.m + keep(&b); }
    return s;
}
// Nested: what is invariant in both leaves both.
nested -> long {
    v: Vec<long>;
    for i in 0..10 { v.push(i); }
    t: long = 0;
    for r in 0..3 { for j in 0..v.len() { t = t + v[j] + r; } }
    return t;                              // 3 * 45 + 10 * (0 + 1 + 2)
}
// A loop entered by a jump as well as by falling in (`continue` to the top, an early skip).
jumpy n:long -> long {
    b: Box = Box { n: 5, m: 1 };
    s: long = 0;
    i: long = 0;
    if (n > 100) { return 0; }
    while (i < n) {
        i = i + 1;
        if (i % 2 == 0) { continue; }
        s = s + b.n + b.m;
    }
    return s;
}
main -> int {
    if (stored() != 25) { return 1; }
    if (called() != 88) { return 2; }
    if (gHits != 4) { return 3; }
    if (aliased() != 26) { return 4; }
    v: Vec<long>;
    v.push(1); v.push(2); v.push(3);
    if (invariant(&v, 2, 3) != 6 * 5 + 3 * 8) { return 5; }
    if (nested() != 135 + 30) { return 6; }
    if (jumpy(7) != 24) { return 7; }
    if (jumpy(0) != 0) { return 8; }
    return 0;
}
