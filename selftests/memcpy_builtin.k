// The `memcpy` builtin, declared here as the standard library declares it: one `rep movsb` at
// run time and a byte loop in the evaluator (a global built through it). Lengths of none, one,
// a word and a run past it; operands crowded out of registers by values live across the copy;
// and a copy inside a callee, which its caller must see.
pub unsafe builtin memcpy dst:long src:long n:long -> void;

struct Pair { a: long, b: long }

copied -> long {
    src: [u8; 40];
    dst: [u8; 40];
    for i in 0..40 { src[i] = (i * 7 + 3) as u8; dst[i] = 0; }
    unsafe {
        memcpy(&dst as long, &src as long, 0);
        memcpy(&dst as long, &src as long, 1);
        memcpy(&dst as long + 1, &src as long + 1, 8);
        memcpy(&dst as long + 9, &src as long + 9, 31);
    }
    s: long = 0;
    for i in 0..40 { if (dst[i] != src[i]) { return 0 - 1 - i; } s = s + (dst[i] as long); }
    return s;
}

// More values live across the copy than there are registers the copy leaves alone, so some would
// sit in rsi, rdi or rcx; the function is too big to be inlined and is called twice, with a
// value the compiler cannot fold.
var gK: long = 9;
crowded k:long -> long {
    s: long = 0;
    for i in 0..k { s = s + i * 3 + 1; if (s > 1000) { s = s - 7; } }
    a: long = k + 1; b: long = k * 3; c: long = k ^ 5; d: long = k + 11; e: long = k * 7;
    f: long = k - 2; g: long = k * 13; h: long = k + 17; j: long = k * 19; m: long = k ^ 23;
    n: long = k * 29; o: long = k + 31; q: long = k ^ 37; u: long = k * 41;
    x: Pair = Pair { a: a + b, b: c + d };
    y: Pair = Pair { a: 0, b: 0 };
    unsafe { memcpy(&y as long, &x as long, 16); }
    return a + b + c + d + e + f + g + h + j + m + n + o + q + u + y.a + y.b + s;
}
expectCrowded k:long -> long {
    s: long = 0;
    for i in 0..k { s = s + i * 3 + 1; if (s > 1000) { s = s - 7; } }
    return (k + 1) + k * 3 + (k ^ 5) + (k + 11) + k * 7 + (k - 2) + k * 13 + (k + 17) + k * 19 + (k ^ 23)
        + k * 29 + (k + 31) + (k ^ 37) + k * 41 + (k + 1 + k * 3) + ((k ^ 5) + k + 11) + s;
}

// A copy through the address it is handed, in a function too big to be inlined, called twice and
// writing nothing else: what its caller knew of the bytes there ends at the call, by its summary.
unsafe setWord p:*long v:long -> long {
    s: long = 0;
    for i in 0..v { s = s + i * 3 + 1; if (s > 1000) { s = s - 7; } }
    for i in 0..v { s = s ^ (i << 2); }
    memcpy(p as long, &v as long, 8);
    return s;
}
throughCall -> long {
    x: long = 1;
    y: long = 2;
    s: long = 0;
    unsafe { s = setWord(&x as *long, 40) + setWord(&y as *long, 2); }
    if (s < 0) { return 0; }
    return x + y;
}

// The same through an `inout` parameter, whose summary is what tells the caller its struct changed.
copyInto inout dst:Pair src:&Pair -> long {
    s: long = 0;
    for i in 0..src.a { s = s + i * 3 + 1; if (s > 1000) { s = s - 7; } }
    for i in 0..src.b { s = s ^ (i << 2); }
    unsafe { memcpy(&dst as long, &src as long, 16); }
    return s;
}
throughParam -> long {
    d: Pair = Pair { a: 1, b: 2 };
    e: Pair = Pair { a: 40, b: 2 };
    k: long = copyInto(&d, e);
    k = k + copyInto(&d, e);
    if (k < 0) { return 0; }
    return d.a + d.b;
}

folded -> long {
    p: Pair = Pair { a: 40, b: 2 };
    q: Pair = Pair { a: 0, b: 0 };
    unsafe { memcpy(&q as long, &p as long, 16); }
    return q.a + q.b;
}
gFolded: long = folded();

main -> long {
    s: long = copied();
    if (s < 0) { return 1; }
    want: long = 0;
    for i in 0..40 { want = want + (((i * 7 + 3) % 256) as long); }
    if (s != want) { return 2; }
    if (crowded(gK) != expectCrowded(gK) || crowded(gK + 4) != expectCrowded(gK + 4)) { return 3; }
    if (gFolded != 42) { return 4; }
    if (throughCall() != 42) { return 5; }
    if (throughParam() != 42) { return 6; }
    return 0;
}
