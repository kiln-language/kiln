#include <stdlib::vec>

// Element reads and writes as one addressing mode each (`[base + i*scale + d]`), at every width,
// through a field's displacement, for a float, a struct element (no power-of-two stride), nested
// indexing, a sixteen-byte element (a shift by 4, which no mode scales by), an index only the
// access reads inside a loop that calls, and with enough live values that the index and the stored
// value both have no register of their own.

struct P { a: long, b: int, c: u8 }
struct H { pad: long, v: [long; 4] }

w1 xs:[u8] i:long -> long { return xs[i] as long; }
w2 xs:[u16] i:long -> long { return xs[i] as long; }
w4 xs:[int] i:long -> long { return xs[i] as long; }
w8 xs:[long] i:long -> long { return xs[i]; }
neg4 xs:[int] i:long -> long { return xs[i] as long; }
put8 inout xs:[long] i:long v:long -> void { xs[i] = v; }
put1 inout xs:[u8] i:long v:u8 -> void { xs[i] = v; }
fsum xs:[f64] -> f64 { t: f64 = 0.0; for i in 0..xs.len { t = t + xs[i]; } return t; }
pb ps:[P] i:long -> long { return ps[i].b as long + ps[i].c as long; }
field h:&H i:long -> long { return h.v[i]; }

// Twelve values live across the loop, so the allocator runs out and spills some.
pressure xs:[long] -> long {
    a: long = xs[0]; b: long = xs[1]; c: long = xs[2]; d: long = xs[3];
    e: long = a + 1; f: long = b + 2; g: long = c + 3; h: long = d + 4;
    k: long = a * b; m: long = c * d; n: long = e * f; q: long = g * h;
    t: long = 0;
    for i in 0..xs.len {
        j: long = xs.len - 1 - i;
        t = t + xs[i] * a + xs[j] * b + xs[(i + 1) % xs.len] * c;
        xs2: long = xs[i] + xs[j];
        t = t + xs2 + d + e + f + g + h + k + m + n + q;
    }
    return t + a + b + c + d + e + f + g + h + k + m + n + q;
}

grid g:[long] w:long r:long c:long -> long { return g[r * w + c]; }

// Sixteen-byte elements: the index shifted by 4, which no addressing mode scales by.
lenAt xs:[str] i:long -> long { return xs[i].len; }

// An index read by the access alone, inside a loop that calls: it has to stay live around the
// loop for the access, with nothing else reading it.
idv x:long -> long { return x; }
var gSink: long = 0;
unsafe atCol p:*long j:long n:long f:fn(long) -> long -> long {
    t: long = 0;
    w: long = 0;
    r: long = 0;
    while (r < n) {
        v: long = p[j];
        // Values made after the access, which the allocator may give the index's register to if
        // it took the index for dead past the access.
        a: long = v * 3 + r; b: long = a ^ r; c: long = b + v; d: long = c * 5; e: long = d ^ a;
        g: long = e + b; h: long = g * 7; k: long = h ^ c; m: long = k + d + e + g + h;
        t = t + v + f(r);
        w = w + (a ^ b ^ c ^ d ^ e ^ g ^ h ^ k ^ m);
        r = r + 1;
    }
    gSink = w;
    return t;
}

// Fourteen running values: the index and the stored value both end up in the frame, and the
// store needs `rdx` for each.
spill xs:[long] inout ys:[long] -> long {
    a: long = 1; b: long = 2; c: long = 3; d: long = 4; e: long = 5; f: long = 6; g: long = 7;
    h: long = 8; k: long = 9; m: long = 10; n: long = 11; q: long = 12; r: long = 13; s: long = 14;
    for i in 0..xs.len {
        j: long = (i * 5 + 3) % xs.len;
        a = a + b * 3; b = b + c * 5; c = c + d * 7; d = d + e * 11; e = e + f * 13; f = f + g * 17;
        g = g + h * 19; h = h + k * 23; k = k + m * 29; m = m + n * 31; n = n + q * 37; q = q + r * 41;
        r = r + s * 43; s = s + a * 47;
        ys[j] = a + b;
        a = a ^ xs[i]; b = b ^ a; c = c ^ b; d = d ^ c; e = e ^ d; f = f ^ e; g = g ^ f; h = h ^ g;
        k = k ^ h; m = m ^ k; n = n ^ m; q = q ^ n; r = r ^ q; s = s ^ r;
    }
    return a + b + c + d + e + f + g + h + k + m + n + q + r + s;
}

main -> long {
    b1: [u8; 4] = [1, 2, 250, 4];
    if (w1(b1[..], 2) != 250) { return 1; }
    b2: [u16; 3] = [10, 60000, 30];
    if (w2(b2[..], 1) != 60000) { return 2; }
    b4: [int; 3] = [5, -7, 9];
    if (w4(b4[..], 1) != -7 || neg4(b4[..], 2) != 9) { return 3; }
    b8: [long; 3] = [100, 200, 300];
    if (w8(b8[..], 2) != 300) { return 4; }
    put8(&b8[..], 1, -5);
    if (b8[1] != -5 || b8[0] != 100 || b8[2] != 300) { return 5; }
    put1(&b1[..], 3, 77);
    if (b1[3] != 77 || b1[2] != 250) { return 6; }
    fs: [f64; 3] = [1.5, 2.25, 4.0];
    if (fsum(fs[..]) != 7.75) { return 7; }
    ps: [P; 3] = [P { a: 1, b: 2, c: 3 }, P { a: 4, b: -5, c: 6 }, P { a: 7, b: 8, c: 9 }];
    if (pb(ps[..], 1) != 1 || pb(ps[..], 2) != 17) { return 8; }
    hh: H = H { pad: 9, v: [11, 22, 33, 44] };
    if (field(hh, 3) != 44 || field(hh, 0) != 11) { return 9; }
    v: Vec<long> = vec![3, 1, 4, 1, 5, 9, 2, 6];
    if (pressure(v.asSlice()) != 984) { return 10; }
    g: [long; 6] = [1, 2, 3, 4, 5, 6];
    if (grid(g[..], 3, 1, 2) != 6) { return 11; }
    ss: [str; 3] = ["a", "bcd", "ef"];
    if (lenAt(ss[..], 1) != 3 || lenAt(ss[..], 2) != 2) { return 12; }
    cols: [long; 4] = [5, 7, 11, 13];
    t: long = 0;
    t2: long = 0;
    // Called twice with indices known only at run time, so it is compiled as a function of its own.
    unsafe { t = atCol(&cols[0] as *long, cols[0] - 3, 3, &idv); t2 = atCol(&cols[0] as *long, cols[1] - 4, 2, &idv); }
    if (t != 36 || t2 != 27) { return 13; }
    sx: [long; 7] = [3, 1, 4, 1, 5, 9, 2];
    sy: [long; 7] = [0, 0, 0, 0, 0, 0, 0];
    if (spill(sx[..], &sy[..]) != 26269366353976 || sy[3] != 24) { return 14; }
    return 0;
}
