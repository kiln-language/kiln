// Floats live across calls to a function declared without a body, linked from a NASM object that
// writes over every `xmm` register System V lets it (`xmm_clobber.asm`): called directly and through
// a fn value. Neither call may keep a float in `xmm12`-`xmm14`. And the stack is 16-aligned at a
// call into that object from a function of every frame shape. `scripts/foreign.sh` builds and runs
// it; exit 0 is every answer right.
//
// A Kiln function that calls that object keeps `xmm12`-`xmm14` for its own caller, which may hold
// floats there across the call to it (`keeper`): the call made directly (`viaDirect`), through a
// fn value that may hold the object's function (`viaValue`), and through a fn value made of a raw
// word (`viaWord`).
//
// A Kiln function that calls the object may change every register foreign code may, whatever
// its own lines name (`RegAlloc.siteMask`): `holder` keeps a dozen values across calls to
// `viaGpr`, which calls `gclobber`, which writes garbage over every general register System V
// lets a callee change.

var gV: long = 0;
dyn v:long -> long { gV = v; return gV; }

// x + 1, and every `xmm` register but xmm0 overwritten.
pub clobber x:f64 -> f64;

// `rsp` modulo 16 as it starts: 8 when its caller called it with the stack aligned.
pub entryAlign -> long;

// x + 1, and rcx, rdx, rsi, rdi and r8 to r11 overwritten.
pub gclobber x:long -> long;

// Callers of each shape, each keeping its parameters across the call: no frame and no saved
// register, no frame and one to four saved registers, more values than those (a frame for the
// spill), a float, a test made before the prologue, and an indirect call (a frame for the callee).
a0 -> long { return entryAlign() * 1000; }
a1 x:long -> long { return entryAlign() * 1000 + x; }
a2 x:long y:long -> long { return entryAlign() * 1000 + x + y; }
a3 x:long y:long z:long -> long { return entryAlign() * 1000 + x + y + z; }
a4 w:long x:long y:long z:long -> long { return entryAlign() * 1000 + w + x + y + z; }
a5 v:long w:long x:long y:long z:long -> long { return entryAlign() * 1000 + v + w + x + y + z; }
af x:f64 -> long { return entryAlign() * 1000 + (x as long); }
ag n:long -> long {
    if (n < 0) { return 0; }
    return entryAlign() * 1000 + n;
}
ai f:fn() -> long x:long -> long { return f() * 1000 + x; }

direct n:long -> long {
    a: f64 = dyn(n) as f64;
    b: f64 = a * 2.0;
    c: f64 = a + 0.5;
    s: f64 = 0.0;
    for k in 0..n {
        r: f64 = clobber(a);
        s = s + r + a + b + c;
    }
    return (s * 10.0) as long;
}

through f:fn(f64) -> f64 n:long -> long {
    a: f64 = dyn(n) as f64;
    b: f64 = a * 2.0;
    c: f64 = a + 0.5;
    s: f64 = 0.0;
    for k in 0..n {
        r: f64 = f(a);
        s = s + r + a + b + c;
    }
    return (s * 10.0) as long;
}

// Each too large to be copied into its callers, and each holding no float across its call.
var gW: long = 0;
var gCalls: long = 0;
var gFn: fn(f64) -> f64 = &clobber;
viaDirect x:f64 -> f64 {
    gCalls = gCalls + 1; gW = gW * 3 + gCalls; gW = gW ^ 5; gW = gW + 7; gW = gW * 5; gW = gW ^ 9;
    gW = gW + 1; gW = gW * 3; gW = gW ^ 5; gW = gW + 7; gW = gW - 2; gW = gW * 5; gW = gW ^ 9;
    return clobber(x) - 1.0;
}
viaValue x:f64 -> f64 {
    gCalls = gCalls + 1; gW = gW * 3 + gCalls; gW = gW ^ 5; gW = gW + 7; gW = gW * 5; gW = gW ^ 9;
    gW = gW + 1; gW = gW * 3; gW = gW ^ 5; gW = gW + 7; gW = gW - 2; gW = gW * 5; gW = gW ^ 9;
    return gFn(x) - 1.0;
}
viaWord x:f64 -> f64 {
    gCalls = gCalls + 1; gW = gW * 3 + gCalls; gW = gW ^ 5; gW = gW + 7; gW = gW * 5; gW = gW ^ 9;
    gW = gW + 1; gW = gW * 3; gW = gW ^ 5; gW = gW + 7; gW = gW - 2; gW = gW * 5; gW = gW ^ 9;
    r: f64 = 0.0;
    unsafe {
        w: long = (&gFn as *long)[0];
        f: fn(f64) -> f64 = w as fn(f64) -> f64;
        r = f(x);
    }
    return r - 1.0;
}

// Small, with a loop so it stays a call: its own lines name few registers.
viaGpr x:long -> long {
    s: long = x;
    for i in 0..(x & 1) + 1 { s = s + i; }
    return gclobber(s) - 1;
}
holder k:long -> long {
    v1: long = gV + k + 1; v2: long = gV + k * 2 + 2; v3: long = gV + k * 3 + 3;
    v4: long = gV + k * 4 + 4; v5: long = gV + k * 5 + 5; v6: long = gV + k * 6 + 6;
    v7: long = gV + k * 7 + 7; v8: long = gV + k * 8 + 8; v9: long = gV + k * 9 + 9;
    v10: long = gV + k * 10 + 10; v11: long = gV + k * 11 + 11; v12: long = gV + k * 12 + 12;
    r: long = viaGpr(k);
    r = r + viaGpr(r & 7) + v1 + v2 * 2 + v3 * 3 + v4 * 4;
    r = r + viaGpr(r & 3) + v5 * 5 + v6 * 6 + v7 * 7 + v8 * 8;
    return r + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 * 9 + v10 * 10 + v11 * 11 + v12 * 12;
}

// Three floats held across each call, in `xmm12`-`xmm14` where they are kept.
keeper which:long n:long -> long {
    a: f64 = dyn(n) as f64;
    b: f64 = a * 2.0;
    c: f64 = a + 0.5;
    s: f64 = 0.0;
    for k in 0..n {
        r: f64 = 0.0;
        if (which == 0) { r = viaDirect(a); } else if (which == 1) { r = viaValue(a); } else { r = viaWord(a); }
        s = s + r + a + b + c;
    }
    return (s * 10.0) as long;
}

main -> int {
    // each step: a + a + 2a + (a + 0.5) = 5a + 0.5, a = 7: 35.5, seven steps: 248.5
    if (keeper(0, 7) != 2485) { return 10; }
    if (keeper(1, 7) != 2485) { return 11; }
    if (keeper(2, 7) != 2485) { return 12; }
    if (viaDirect(2.0) != 2.0 || viaValue(2.0) != 2.0 || viaWord(2.0) != 2.0) { return 13; }
    if (holder(dyn(5)) != 4560) { return 14; }
    n: long = 7;
    // each step: (a + 1) + a + 2a + (a + 0.5) = 5a + 1.5, a = 7: 36.5, seven steps: 255.5
    if (direct(n) != 2555) { return 1; }
    if (through(&clobber, n) != 2555) { return 2; }
    f0: fn() -> long = &a0;
    f1: fn(long) -> long = &a1;
    f2: fn(long, long) -> long = &a2;
    f3: fn(long, long, long) -> long = &a3;
    f4: fn(long, long, long, long) -> long = &a4;
    f5: fn(long, long, long, long, long) -> long = &a5;
    ff: fn(f64) -> long = &af;
    fg: fn(long) -> long = &ag;
    fi: fn(fn() -> long, long) -> long = &ai;
    if (f0() != 8000 || f1(1) != 8001 || f2(1, 2) != 8003 || f3(1, 2, 3) != 8006) { return 3; }
    if (f4(1, 2, 3, 4) != 8010 || f5(1, 2, 3, 4, 5) != 8015 || ff(2.5) != 8002) { return 4; }
    if (fg(5) != 8005 || fg(-1) != 0 || fi(&entryAlign, 7) != 8007) { return 5; }
    return 0;
}
