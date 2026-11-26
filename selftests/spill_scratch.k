// Values the allocator left in the frame for want of a register, each written by one
// instruction and read by one a few later, kept in `rax` or `rdx` in between instead
// (`RegAlloc.spillScratch`). Each function holds more values through its loop than there are
// registers, so its short-lived ones are what is left over: two loaded words compared, a limit
// computed and compared at once, a value converted and stored, a hash shifted and multiplied,
// a bounds check's index. Every result is held to the value the frame gave.
probe a:[u32] b:[u32] n:long s0:long s1:long s2:long s3:long -> long {
    x0: long = s0; x1: long = s1; x2: long = s2; x3: long = s3;
    x4: long = s0 ^ s1; x5: long = s1 ^ s2; x6: long = s2 ^ s3; x7: long = s3 ^ s0;
    x8: long = s0 + 1; x9: long = s1 + 2; x10: long = s2 + 3; x11: long = s3 + 4;
    hits: long = 0;
    i: long = 0;
    while (i < n) {
        j: long = (i * 7 + x3) & (n - 1);
        if ((a[i] as long) == (b[j] as long)) { hits = hits + (x0 & 255); }
        if (x5 > n * 13 - 17) { hits = hits + 1; }
        x0 = x0 + x1; x1 = x1 ^ x2; x2 = x2 + x3; x3 = x3 ^ x4;
        x4 = x4 + x5; x5 = (x5 ^ x6) & 1023; x6 = x6 + x7; x7 = x7 ^ (i + 1);
        x8 = x8 + x9; x9 = x9 ^ x10; x10 = x10 + x11; x11 = x11 ^ x8;
        i = i + 1;
    }
    return hits + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11;
}

// A table filled with converted values while many others stay live; one conversion is also read
// at its full width, so it must still be made.
fill inout h:[u32] n:long s:long -> long {
    p: long = s; q: long = s * 3; r: long = s ^ 77; u: long = s + 5; v: long = s - 9;
    w: long = s * 11; y: long = s ^ 1234; z: long = s + 99;
    sum: long = 0;
    for i in 0..n {
        k: long = ((((p + i) as u64) << 24) * 889523592379 >> 58) as long;
        h[k] = (q + i) as u32;
        c: u32 = (r * i) as u32;
        h[(k + 1) & 63] = c;
        sum = sum + (c as long);
        p = p + q; q = q ^ r; r = r + u; u = u ^ v; v = v + w; w = w ^ y; y = y + z; z = z ^ i;
    }
    for i in 0..64 { sum = sum + (h[i] as long) * (i + 1); }
    return sum + p + q + r + u + v + w + y + z;
}

// Values in the frame compared and added where they lie (`cmp rbx, [rbp - 64]`), after a call
// and after a store through a pointer lent to it: a temp's slot holds what its last write left.
var gTick: long = 0;
poke inout cell:long v:long -> long {
    for k in 0..(v & 3) + 1 { cell = cell + k; gTick = gTick ^ k; }
    cell = cell ^ v;
    return cell & 255;
}
across n:long s:long -> long {
    cell: long = s;
    x0: long = s; x1: long = s * 3; x2: long = s ^ 77; x3: long = s + 5; x4: long = s - 9;
    x5: long = s * 11; x6: long = s ^ 1234; x7: long = s + 99; x8: long = s * 7; x9: long = s ^ 5;
    hits: long = 0;
    for i in 0..n {
        lim: long = (x3 + i) & 255;
        r: long = poke(&cell, x5 + i);
        if (r > lim) { hits = hits + 1; }
        if (cell > x7) { hits = hits + 2; }
        hits = hits + (x9 & 15);
        x0 = x0 + x1; x1 = x1 ^ x2; x2 = x2 + x3; x3 = x3 ^ x4; x4 = x4 + x5;
        x5 = x5 ^ x6; x6 = x6 + x7; x7 = x7 ^ i; x8 = x8 + x9; x9 = x9 ^ x0;
    }
    return hits + cell + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9;
}

// A difference with a constant too wide for an immediate, compared at once: in rdx its constant
// is fetched into rdx too, so it is computed there only from operands already in registers.
unsafe below p:*long n:long s0:long -> long {
    x0: long = s0; x1: long = s0 * 3; x2: long = s0 ^ 77; x3: long = s0 + 5; x4: long = s0 - 9;
    x5: long = s0 * 11; x6: long = s0 ^ 1234; x7: long = s0 + 99; x8: long = s0 * 7; x9: long = s0 ^ 5;
    x10: long = s0 + 1; x11: long = s0 - 1;
    hits: long = 0;
    for i in 0..n {
        if (p[i] < x0 - 5000000000) { hits = hits + 1; }
        if (p[i] > x3 + 7000000000) { hits = hits + 2; }
        x0 = x0 + x1; x1 = x1 ^ x2; x2 = x2 + x3; x3 = x3 ^ x4; x4 = x4 + x5; x5 = x5 ^ x6;
        x6 = x6 + x7; x7 = x7 ^ i; x8 = x8 + x9; x9 = x9 ^ x10; x10 = x10 + x11; x11 = x11 ^ x0;
    }
    return hits + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11;
}

// A value stored through a pointer left in the frame: the pointer is fetched into rax, so the
// value is not kept there (it goes to rdx).
unsafe stash q:*long n:long s0:long -> long {
    x0: long = s0; x1: long = s0 * 3; x2: long = s0 ^ 77; x3: long = s0 + 5; x4: long = s0 - 9;
    x5: long = s0 * 11; x6: long = s0 ^ 1234; x7: long = s0 + 99; x8: long = s0 * 7; x9: long = s0 ^ 5;
    x10: long = s0 + 1; x11: long = s0 - 1;
    for i in 0..n {
        q[i] = x0 * 3 + x5;
        x0 = x0 + x1; x1 = x1 ^ x2; x2 = x2 + x3; x3 = x3 ^ x4; x4 = x4 + x5; x5 = x5 ^ x6;
        x6 = x6 + x7; x7 = x7 ^ i; x8 = x8 + x9; x9 = x9 ^ x10; x10 = x10 + x11; x11 = x11 ^ x0;
    }
    s: long = 0;
    for i in 0..n { s = s * 31 + q[i]; }
    return s + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11;
}

main -> int {
    a: [u32; 64];
    b: [u32; 64];
    for i in 0..64 {
        a[i] = ((i * 37) % 11) as u32;
        b[i] = ((i * 53) % 11) as u32;
    }
    h: [u32; 64];
    for i in 0..64 { h[i] = 0; }
    r1: long = probe(a[..], b[..], 64, 3, 5, 7, 11);
    r2: long = probe(a[..], b[..], 32, -1, 9, 1 << 40, 6);
    r3: long = fill(&h, 200, 17);
    r4: long = across(50, 3);
    r5: long = across(9, -7);
    if (r1 != 495897584005520) { return 1; }
    if (r2 != 7946948988284588172) { return 2; }
    if (r3 != 2840440796197) { return 3; }
    if (r4 != -11514891) { return 4; }
    if (r5 != -19919) { return 5; }
    v: [long; 8] = [0, -9000000000, 9000000000, 5, -5, 123456789012, -123456789012, 77];
    r6: long = 0;
    unsafe { r6 = below(&v[0] as *long, 8, 3) + below(&v[0] as *long, 8, -6000000000); }
    if (r6 != -344956434024) { return 6; }
    w: [long; 8] = [0, 0, 0, 0, 0, 0, 0, 0];
    r7: long = 0;
    unsafe { r7 = stash(&w[0] as *long, 8, 3) + stash(&w[0] as *long, 8, -6000000000); }
    if (r7 != 1785002695073037348) { return 7; }
    return 0;
}
