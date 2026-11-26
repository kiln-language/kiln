// A call in a loop to a body too large to copy whose head returns by a short path gets that head
// copied, every other way out of it a call of the whole function (`partialPlan`). Each path is
// taken here: the short returns, the call for the long and the very short slices, a head that
// writes its parameter, one that returns nothing, a float result, and a call that reaches the
// head through a body copied into the loop.
same xs:[long] ys:[long] -> bool {
    n: long = xs.len;
    if (ys.len != n) { return false; }
    if (n >= 8) {
        for i in 0..n { if (xs[i] != ys[i]) { return false; } }
        return true;
    }
    if (n >= 2) { return xs[n - 1] == ys[n - 1]; }
    k: long = 0;
    while (k < n) { if (xs[k] != ys[k]) { return false; } k += 1; }
    return true;
}
// Writes its parameter in the head, and returns it or loops.
clampSum from:long lim:long -> long {
    if (from < 0) { from = 0; }
    if (from >= lim) { return from * 2; }
    s: long = 0;
    i: long = from;
    while (i < lim) { s += i; i += 1; }
    return s;
}
var gTicks: long = 0;
// Returns nothing: an early return, else a loop that writes a global.
tick n:long -> void {
    if (n <= 0) { return; }
    for i in 0..n { gTicks += i; }
}
// A float result by the short path.
scaled x:double n:long -> double {
    if (n == 0) { return x * 0.5; }
    t: double = x;
    for i in 0..n { t = t * 1.5; }
    return t;
}
// Its head writes memory first, so it has none worth copying: a copy would count twice where the
// call it leaves for counts again.
var gCalls: long = 0;
counted n:long -> long {
    gCalls += 1;
    if (n <= 1) { return n; }
    s: long = 0;
    for i in 0..n { s += i; }
    return s;
}
// Writes its parameter before it leaves for the call, which must still get the argument.
shiftSum from:long lim:long -> long {
    if (from < 0) { from = from + 10; }
    if (from >= lim) { return from; }
    s: long = 0;
    i: long = from;
    while (i < lim) { s += i; i += 1; }
    return s;
}
// Small enough to copy whole; its call to `same` sits in the caller's loop once copied.
local sameTail xs:[long] ys:[long] -> bool { return same(xs[1..], ys[1..]); }
main -> int {
    a: [long; 10] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    b: [long; 10] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    c: [long; 10] = [1, 2, 3, 4, 5, 6, 7, 0, 9, 10];
    hits: long = 0;
    for len in 0..11 {
        if (same(a[..len], b[..len])) { hits += 1; }        // 11
        if (same(a[..len], c[..len])) { hits += 100; }      // lengths 0 to 7
        if (same(a[..len], b[..10 - len])) { hits += 10000; } // only len 5
        if (len >= 1 && sameTail(a[..len], b[..len])) { hits += 1000000; }
    }
    if (hits != 11 + 800 + 10000 + 10000000) { return 1; }
    t: long = 0;
    for k in 0..6 { t += clampSum(k - 2, 3); }
    // k-2 = -2,-1,0,1,2,3: 0+1+2, 0+1+2, 0+1+2, 1+2, 2, 3*2
    if (t != 3 + 3 + 3 + 3 + 2 + 6) { return 2; }
    // A second call of each, outside a loop, so that none is copied whole for its one call.
    if (clampSum(-5, 0) != 0 || clampSum(1, 4) != 6) { return 5; }
    tick(0);
    if (scaled(4.0, 0) != 2.0) { return 6; }
    starts: [long; 4] = [-15, -1, 2, 7];
    u: long = 0;
    for k in 0..4 { u = u * 100 + shiftSum(starts[k], 3) + 50; c0: long = counted(k); u += c0; }
    // -15 becomes -5: -5 to 2 sums to -12; -1 becomes 9: 9; 2: 2; 7: 7. counted: 0, 1, 1, 3.
    if (u != (((-12 + 50) * 100 + 9 + 50 + 1) * 100 + 2 + 50 + 1) * 100 + 7 + 50 + 3 || gCalls != 4) { return 7; }
    if (shiftSum(-30, -25) != -20 || counted(2) != 1) { return 8; }
    for k in 0..4 { tick(k - 1); }
    // tick(-1), tick(0) return early; tick(1): 0; tick(2): 0+1
    if (gTicks != 1) { return 3; }
    f: double = 0.0;
    for k in 0..3 { f = f + scaled(2.0, k); }
    // 1.0 + 3.0 + 4.5
    if (f != 8.5) { return 4; }
    return 0;
}
