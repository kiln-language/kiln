// Calls whose callee is not named stay calls that may change every register a callee need not
// keep (`RegAlloc.siteMask`): through a fn value, through a fn value made of a raw word, and a
// trait method through its vtable. Each target here writes many registers; the caller keeps a
// dozen values across each call, besides calls to `quiet`, which leaves most registers alone, so
// some of those values sit in caller-saved registers across its calls but not across the others.

var gSink: long = 0;

quiet x:long -> long {
    s: long = x;
    for i in 0..(x & 1) + 1 { s = s + i; }
    return s;
}

// Ten values at once: every caller-saved register a value can have.
busy x:long -> long {
    a: long = gSink + x + 1; b: long = a * 3 + x; c: long = b * 5 + a; d: long = c * 7 + b;
    e: long = d * 11 + c; f: long = e * 13 + d; g: long = f * 17 + e; h: long = g * 19 + f;
    i: long = h * 23 + g; j: long = i * 29 + h;
    for k in 0..(x & 1) + 1 { a = a + k; }
    return (a ^ b ^ c ^ d ^ e ^ f ^ g ^ h ^ i ^ j) & 65535;
}

struct Loud { n: long }
struct Hush { n: long }
trait Act { act &self x:long -> long; }
methods Loud for Act { act &self x:long -> long { return busy(x + self.n); } }
methods Hush for Act { act &self x:long -> long { return quiet(x + self.n); } }

held f:fn(long) -> long o:Act k:long -> long {
    v1: long = gSink + k + 1; v2: long = gSink + k * 2 + 2; v3: long = gSink + k * 3 + 3;
    v4: long = gSink + k * 4 + 4; v5: long = gSink + k * 5 + 5; v6: long = gSink + k * 6 + 6;
    v7: long = gSink + k * 7 + 7; v8: long = gSink + k * 8 + 8; v9: long = gSink + k * 9 + 9;
    v10: long = gSink + k * 10 + 10; v11: long = gSink + k * 11 + 11; v12: long = gSink + k * 12 + 12;
    r: long = quiet(k);
    r = r + f(k) + v1 + v2 * 2 + v3 * 3;
    r = r + quiet(r & 7) + v4 * 4 + v5 * 5 + v6 * 6;
    r = r + o.act(k) + v7 * 7 + v8 * 8 + v9 * 9;
    w: long = 0;
    unsafe { w = (&f as *long)[0]; }
    g: fn(long) -> long = &quiet;
    unsafe { (&g as *long)[0] = w; }
    r = r + g(k + 1) + v10 * 10 + v11 * 11 + v12 * 12;
    return r + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 + v10 + v11 + v12;
}

main -> long {
    gSink = quiet(0);
    loud: Loud = Loud { n: 3 };
    hush: Hush = Hush { n: 4 };
    if (held(&busy, loud, 5) != 133635) { return 1; }
    if (held(&quiet, hush, 6) != 5132) { return 2; }
    if (held(&busy, hush, 7) != 59548) { return 3; }
    return 0;
}
