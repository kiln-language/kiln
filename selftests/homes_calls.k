#include <stdlib::{io, recover}>

// Values live across calls, more of them than the callee-saved registers hold, so some are kept
// in caller-saved registers with a home in the frame (`RegAlloc.homed`): written there wherever
// they are written, read back after every call they are live across. Calls in loops, calls made
// only on some paths, values written again between calls, a parameter kept that way, floats among
// them, and a `recover` whose handler reads what was kept around the call that raised.

var gK: long = 3;
var gF: f64 = 0.5;
var gSink: long = 0;

// Big enough, and with a loop, so it stays a call; it writes every caller-saved register's worth
// of work.
churn x:long -> long {
    s: long = x;
    for i in 0..(x & 3) + 2 { s = s * 31 + i; gSink = gSink ^ s; }
    return s & 1023;
}

// Six values and a counter live across two calls a turn, one of them on some turns only.
many n:long -> long {
    a: long = gK + 1;
    b: long = gK * 2 + 5;
    c: long = gK * 7 - 1;
    d: long = gK * 11 + 2;
    e: long = gK * 13 + 9;
    f: long = gK * 17 + 4;
    s: long = 0;
    for i in 0..n {
        s += churn(i) + a;
        s += b ^ c;
        if (i % 3 == 0) { s += churn(s) - d; }
        s += e + f;
        a = a + 1;
    }
    return s + a + b + c + d + e + f;
}

// A parameter and floats kept across calls.
mixed p:long q:long r:long -> long {
    x: f64 = (gK as f64) * gF;
    y: f64 = x + 1.25;
    u: long = p * 3;
    v: long = q * 5;
    w: long = r * 7;
    t: long = churn(p) + churn(q);
    t += churn(r) + (u ^ v) + w;
    z: f64 = x * y + (t as f64);
    return t + p + q + r + u + v + w + (z as long);
}

deep n:long -> long {
    if (n == 0) { unsafe { raise(); } }
    return churn(n) + deep(n - 1);
}

// What the handler reads is kept in the frame; what is live only around the body is not, and
// must be right after the body too.
guarded k:long -> long {
    a: long = k + 1;
    b: long = k * 2;
    c: long = k * 3;
    d: long = k * 4;
    e: long = k * 5;
    hit: long = 0;
    unsafe {
        recover {
            hit = churn(a) + churn(b);
            hit = hit + deep(4);
        } else {
            hit = hit * 2 + a + b + c + d + e;
        }
    }
    return hit + churn(c) + d + e;
}

main -> long {
    if (many(40) != 31258) { return 1; }
    if (mixed(4, 9, 13) != 4236) { return 2; }
    if (guarded(6) != 1781) { return 3; }
    return 0;
}
