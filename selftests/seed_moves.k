// Parameters reaching the registers the allocator gave them, as one parallel move in the prologue:
// a parameter whose new register is where another argument arrived waits until that one has moved.
// Every function is called through a fn value or recurses, so none is copied into its caller.

var gSink: long = 0;
id x:long -> long { gSink = gSink + 1; return x; }

// The first parameter is never read, so its register is free for the second one's temp: moving
// the first there would overwrite the second.
second a:long b:long -> long { return b * 2; }
// Each parameter moves into the register the next one arrives in.
chain a:long b:long c:long d:long -> long { return a * 1000 + b * 100 + c * 10 + d; }
// Unused parameters between used ones.
gaps a:long b:long c:long d:long e:long -> long { return a * 10 + e; }
// Narrow types arrive canonical and must stay so.
narrow a:u8 b:i16 c:int d:u32 -> long {
    return (a as long) * 1000000 + (b as long) * 1000 + (c as long) + (d as long);
}
// Floats between integers: the two classes are counted apart.
mixed a:long x:f64 b:long y:f64 c:long -> f64 { return (a as f64) * x + (b as f64) * y + (c as f64); }
// Twelve integers and ten floats: the last two of each class come on the stack.
many a0:long a1:long a2:long a3:long a4:long a5:long a6:long a7:long a8:long a9:long a10:long a11:long
     f0:f64 f1:f64 f2:f64 f3:f64 f4:f64 f5:f64 f6:f64 f7:f64 f8:f64 f9:f64 -> long {
    s: long = a0 + 2 * a1 + 3 * a2 + 4 * a3 + 5 * a4 + 6 * a5 + 7 * a6 + 8 * a7 + 9 * a8 + 10 * a9 + 11 * a10 + 12 * a11;
    t: f64 = f0 + 2.0 * f1 + 3.0 * f2 + 4.0 * f3 + 5.0 * f4 + 6.0 * f5 + 7.0 * f6 + 8.0 * f7 + 9.0 * f8 + 10.0 * f9;
    return s * 1000 + (t as long);
}
// The same, with the stack parameters and a float live across a call.
manyAcross a0:long a1:long a2:long a3:long a4:long a5:long a6:long a7:long a8:long a9:long a10:long a11:long
           f0:f64 f1:f64 f2:f64 f3:f64 f4:f64 f5:f64 f6:f64 f7:f64 f8:f64 f9:f64 -> long {
    k: long = id(a11);
    return k * 100 + a10 * 10 + a0 + (f9 as long) + (f0 as long) + a9;
}
// Parameters live across calls, in callee-saved registers.
across a:long b:long c:long -> long {
    x: long = id(a);
    y: long = id(b);
    return x * 100 + y * 10 + c + a + b;
}
// Rotated at every level of a recursion: each level's arguments arrive where its caller's
// parameters were.
rotate a:long b:long c:long n:long -> long {
    if (n == 0) { return a * 100 + b * 10 + c; }
    return rotate(c, a, b, n - 1) + 0 * id(n);
}
// A pointer and a length, the shape of most library code.
sumOf p:*long n:long -> long {
    s: long = 0;
    for i in 0..n { unsafe { s += *(p + i); } }
    return s;
}

main -> int {
    s2: fn(long, long) -> long = &second;
    ch: fn(long, long, long, long) -> long = &chain;
    gp: fn(long, long, long, long, long) -> long = &gaps;
    nw: fn(u8, i16, int, u32) -> long = &narrow;
    mx: fn(long, f64, long, f64, long) -> f64 = &mixed;
    ac: fn(long, long, long) -> long = &across;
    if (s2(5, 7) != 14) { return 1; }
    if (ch(1, 2, 3, 4) != 1234) { return 2; }
    if (gp(3, 9, 9, 9, 4) != 34) { return 3; }
    if (nw(200, -300 as i16, -70000, 4000000000 as u32) != 199700000 + 3999930000) { return 4; }
    if (mx(2, 1.5, 3, 0.25, 7) != 10.75) { return 5; }
    if (many(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0) != 650055) { return 6; }
    if (manyAcross(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 2.5, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 9.5) != 1332) { return 7; }
    if (ac(1, 2, 3) != 126) { return 8; }
    if (rotate(1, 2, 3, 1) != 312 || rotate(1, 2, 3, 2) != 231 || rotate(1, 2, 3, 3) != 123) { return 9; }
    xs: [long; 4] = [1, 2, 3, 4];
    so: fn(*long, long) -> long = &sumOf;
    unsafe { if (so(&xs[0], 4) != 10) { return 10; } }
    return 0;
}
