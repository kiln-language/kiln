#include <stdlib::{io, recover}>

// The registers a `raise` would leave wrong. r12 to r15 and xmm12 to xmm14 are callee-saved
// between Kiln functions, and the frames a `raise` abandons saved them and never put them back.
// `keep` holds five integers and a float across its call to `guarded`, which is what the
// allocator keeps in those registers; `guarded` holds its own across its `recover` and reads
// them in the handler; `churn` fills the same registers with values of its own on the way down
// to the `raise`.

churn n:long f:f64 -> long {
    a: long = n * 3 + 1;
    b: long = n * 5 + 2;
    c: long = n * 7 + 3;
    d: long = n * 11 + 4;
    g: f64 = f * 2.5;
    if (n == 0) { unsafe { raise(); } }
    r: long = churn(n - 1, g);
    return r + a + b + c + d + (g as long);
}

guarded seed:long -> long {
    p: long = seed + 1;
    q: long = seed + 2;
    r: long = seed + 3;
    s: long = seed + 4;
    h: f64 = (seed as f64) * 0.5;
    hit: long = 0;
    unsafe {
        recover {
            hit = 1;
            churn(6, 1.25);
            hit = 2;
        } else {
            hit = hit * 100 + p + q + r + s + (h as long);
        }
    }
    return hit + p + q + r + s + (h as long);
}

// Read from a `var` global, so nothing folds them into constants and they have to be held.
var gBase: long = 1000;
var gScale: f64 = 0.25;

keep -> long {
    v1: long = gBase + 1;
    v2: long = gBase * 2 + 2;
    v3: long = gBase * 3 + 3;
    v4: long = gBase * 4 + 4;
    v5: long = gBase * 5 + 5;
    fl: f64 = (gBase as f64) * gScale;
    got: long = guarded(10);
    // 100 + 11 + 12 + 13 + 14 + 5 in the handler, and 55 more after it
    if (got != 210) { return 1; }
    if (v1 != 1001 || v2 != 2002 || v3 != 3003 || v4 != 4004 || v5 != 5005) { return 2; }
    if (fl != 250.0) { return 3; }
    return v1 + v2 + v3 + v4 + v5 - 15015;
}

main -> long {
    for i in 0..3 {
        r: long = keep();
        if (r != 0) { return r; }
    }
    return 0;
}
