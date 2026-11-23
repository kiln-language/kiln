// A call on the cold way to a call that never returns (`Emitter.coldRun`, written past the
// function's `ret`): the values live across it, more than the callee-saved registers hold, some
// with a home in the frame, are read back after it there too (`reloadAfter`), and what the way
// computes from them is the exit code.
var gK: long = 3;
// A loop called from two places (so never copied into its callers) that uses every
// caller-saved register.
note x:long -> long {
    a: long = x;
    b: long = x * 3;
    c: long = x * 5;
    d: long = x * 7;
    e: long = x * 11;
    f: long = x * 13;
    g: long = x * 17;
    h: long = x * 19;
    for k in 0..x { a += b; b += c; c += d; d += e; e += f; f += g; g += h; h += a; }
    return (a ^ b ^ c ^ d ^ e ^ f ^ g ^ h) & 255;
}
bail code:long -> never { exit(code); }
pick n:long -> long {
    a: long = gK + n;
    b: long = gK * 2 + n;
    c: long = gK * 3 + n;
    d: long = gK * 5 + n;
    e: long = gK * 7 + n;
    f: long = gK * 11 + n;
    g: long = gK * 13 + n;
    h: long = gK * 17 + n;
    if (n > 5) {
        m: long = note(n);
        bail((m + a + b + c + d + e + f + g + h) % 200);
    }
    return a + b + c + d + e + f + g + h;
}
main -> long {
    p: fn(long) -> long = &pick;
    if (p(2) != 3 * 59 + 16) { return 1; }
    // A second call, so `note` stays a function of its own.
    if (note(0) != 0) { return 3; }
    p(9);
    return 2;
}
