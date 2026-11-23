#include <stdlib::{io, recover}>

// Values kept across calls in caller-saved registers the callees leave alone (`RegAlloc.siteMask`),
// where one of the calls raises. The edge into a handler keeps no register: what the handler
// reads is in the frame, and whatever else was live across the call that raised is dead there.
// The handler in the same function (`same`), in the caller (`outer`, the raise coming from
// `middle`), and a caller of a function holding a handler (`top`), which may change anything: a
// raise from below lands in it with whatever the code between left, and it then returns. `boom`
// never returns, so a call to it changes nothing its caller could see; what it writes before it
// raises reaches `top2` through `outer2`, which catches it, and only `outer2`'s holding a handler
// keeps `top2` from trusting registers `boom` wrote.

var gSink: long = 0;

// Each with a loop, so each stays a call, and each writing few registers.
small x:long -> long {
    s: long = x;
    for i in 0..(x & 1) + 1 { s = s + i; }
    return s;
}
thrower n:long -> long {
    s: long = n * 2;
    for i in 0..(n & 1) + 1 { s = s + i; }
    if (n == 0) { unsafe { raise(); } }
    return s;
}

// Ten values at once, then a raise.
boom n:long -> never {
    a: long = gSink + n + 1; b: long = a * 3 + n; c: long = b * 5 + a; d: long = c * 7 + b;
    e: long = d * 11 + c; f: long = e * 13 + d; g: long = f * 17 + e; h: long = g * 19 + f;
    i: long = h * 23 + g; j: long = i * 29 + h;
    gSink = gSink + ((a ^ b ^ c ^ d ^ e ^ f ^ g ^ h ^ i ^ j) & 1);
    unsafe { raise(); }
}
quietThrow n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    if (n == 0) { boom(s); }
    return s;
}
outer2 k:long -> long {
    r: long = 0;
    unsafe {
        recover { r = quietThrow(k) + small(k); } else { r = 0 - 7; }
    }
    return r;
}
top2 k:long -> long {
    v1: long = gSink + k + 1; v2: long = gSink + k * 2 + 2; v3: long = gSink + k * 3 + 3;
    v4: long = gSink + k * 4 + 4; v5: long = gSink + k * 5 + 5; v6: long = gSink + k * 6 + 6;
    v7: long = gSink + k * 7 + 7; v8: long = gSink + k * 8 + 8; v9: long = gSink + k * 9 + 9;
    v10: long = gSink + k * 10 + 10; v11: long = gSink + k * 11 + 11; v12: long = gSink + k * 12 + 12;
    r: long = outer2(k);
    r = r + outer2(k - 1);
    return r + v1 + v2 * 2 + v3 * 3 + v4 * 4 + v5 * 5 + v6 * 6 + v7 * 7 + v8 * 8 + v9 * 9 + v10 * 10 + v11 * 11 + v12 * 12;
}

same k:long -> long {
    a: long = gSink + k + 1;
    b: long = gSink + k * 3 + 2;
    c: long = gSink + k * 5 + 3;
    d: long = gSink + k * 7 + 4;
    e: long = gSink + k * 11 + 5;
    f: long = gSink + k * 13 + 6;
    g: long = gSink + k * 17 + 7;
    h: long = gSink + k * 19 + 8;
    got: long = 0;
    unsafe {
        recover {
            t: long = thrower(k);
            got = t + a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8;
            t = thrower(k - 1);
            got = got + t + a * 8 + b * 7 + c * 6 + d * 5 + e * 4 + f * 3 + g * 2 + h;
        } else {
            got = 0 - got - 1;
        }
    }
    return got;
}

middle k:long -> long {
    a: long = gSink + k * 2 + 1;
    b: long = gSink + k * 4 + 3;
    c: long = gSink + k * 6 + 5;
    d: long = gSink + k * 8 + 7;
    e: long = gSink + k * 10 + 9;
    f: long = gSink + k * 12 + 11;
    r: long = small(k) + a + b + c;
    r = r + thrower(k - 2) * 3 + d + e + f;
    r = r + small(r & 7) + a * b + c * d + e * f;
    return r;
}

outer k:long -> long {
    x: long = k * 3 + gSink;
    y: long = k * 5 + gSink + 1;
    r: long = 0;
    unsafe {
        recover { r = middle(k); } else { r = 0 - 1000 - x; }
    }
    return r + x * 7 + y;
}

top k:long -> long {
    v1: long = gSink + k + 101;
    v2: long = gSink + k * 2 + 102;
    v3: long = gSink + k * 3 + 103;
    v4: long = gSink + k * 4 + 104;
    v5: long = gSink + k * 5 + 105;
    v6: long = gSink + k * 6 + 106;
    v7: long = gSink + k * 7 + 107;
    v8: long = gSink + k * 8 + 108;
    v9: long = gSink + k * 9 + 109;
    v10: long = gSink + k * 10 + 110;
    v11: long = gSink + k * 11 + 111;
    v12: long = gSink + k * 12 + 112;
    r: long = outer(k);
    return r + v1 + v2 * 2 + v3 * 3 + v4 * 4 + v5 * 5 + v6 * 6 + v7 * 7 + v8 * 8 + v9 * 9 + v10 * 10 + v11 * 11 + v12 * 12;
}

main -> long {
    gSink = small(0);
    if (same(5) != 3763) { return 1; }
    if (same(1) != -662) { return 2; }
    if (outer(5) != 6493) { return 3; }
    if (outer(2) != -953) { return 4; }
    if (top(5) != 18193) { return 5; }
    if (top(2) != 8797) { return 6; }
    if (top2(1) != 1297) { return 7; }
    if (top2(4) != 3344) { return 8; }
    return 0;
}
