// A `memcpy` of a constant length up to 128 bytes is written as moves (`emitShortCopy`): words of
// eight bytes and a last word ending where the copy ends, or under eight bytes two moves of four,
// two or one. Every length from 1 to 17 and the edges past it, between misaligned addresses, with
// the bytes on either side of the copy checked untouched; and the same with the addresses crowded
// out of registers, where the bytes go through `xmm15` or the copy falls back to `rep movsb`.
pub unsafe builtin memcpy dst:long src:long n:long -> void;

struct Bufs { s: [u8; 160], d: [u8; 160] }

reset b:&Bufs -> void {
    for i in 0..160 { b.s[i] = (i * 7 + 3) as u8; b.d[i] = 170; }
}
// The copy of `n` bytes from `s + 3` to `d + 5`, and nothing else written.
same b:&Bufs n:long -> bool {
    for i in 0..160 {
        want: u8 = 170;
        if (i >= 5 && i < 5 + n) { want = b.s[i - 2]; }
        if (b.d[i] != want) { return false; }
    }
    return true;
}

lengths b:&Bufs -> long {
    sp: long = 0;
    dp: long = 0;
    unsafe { sp = &b.s as long + 3; dp = &b.d as long + 5; }
    reset(b); unsafe { memcpy(dp, sp, 1); } if (!same(b, 1)) { return 1; }
    reset(b); unsafe { memcpy(dp, sp, 2); } if (!same(b, 2)) { return 2; }
    reset(b); unsafe { memcpy(dp, sp, 3); } if (!same(b, 3)) { return 3; }
    reset(b); unsafe { memcpy(dp, sp, 4); } if (!same(b, 4)) { return 4; }
    reset(b); unsafe { memcpy(dp, sp, 5); } if (!same(b, 5)) { return 5; }
    reset(b); unsafe { memcpy(dp, sp, 6); } if (!same(b, 6)) { return 6; }
    reset(b); unsafe { memcpy(dp, sp, 7); } if (!same(b, 7)) { return 7; }
    reset(b); unsafe { memcpy(dp, sp, 8); } if (!same(b, 8)) { return 8; }
    reset(b); unsafe { memcpy(dp, sp, 9); } if (!same(b, 9)) { return 9; }
    reset(b); unsafe { memcpy(dp, sp, 10); } if (!same(b, 10)) { return 10; }
    reset(b); unsafe { memcpy(dp, sp, 11); } if (!same(b, 11)) { return 11; }
    reset(b); unsafe { memcpy(dp, sp, 12); } if (!same(b, 12)) { return 12; }
    reset(b); unsafe { memcpy(dp, sp, 13); } if (!same(b, 13)) { return 13; }
    reset(b); unsafe { memcpy(dp, sp, 14); } if (!same(b, 14)) { return 14; }
    reset(b); unsafe { memcpy(dp, sp, 15); } if (!same(b, 15)) { return 15; }
    reset(b); unsafe { memcpy(dp, sp, 16); } if (!same(b, 16)) { return 16; }
    reset(b); unsafe { memcpy(dp, sp, 17); } if (!same(b, 17)) { return 17; }
    reset(b); unsafe { memcpy(dp, sp, 31); } if (!same(b, 31)) { return 31; }
    reset(b); unsafe { memcpy(dp, sp, 64); } if (!same(b, 64)) { return 64; }
    reset(b); unsafe { memcpy(dp, sp, 127); } if (!same(b, 127)) { return 127; }
    reset(b); unsafe { memcpy(dp, sp, 128); } if (!same(b, 128)) { return 128; }
    reset(b); unsafe { memcpy(dp, sp, 129); } if (!same(b, 129)) { return 129; }
    reset(b); unsafe { memcpy(dp, sp, 0); } if (!same(b, 0)) { return 130; }
    return 0;
}

// Values live across each copy outnumber the registers a copy leaves alone, so its addresses are
// read from the frame into both scratch registers.
var gK: long = 5;
crowded b:&Bufs k:long -> long {
    a: long = k + 1; c: long = k * 3; e: long = k ^ 5; f: long = k + 11; g: long = k * 7;
    h: long = k - 2; j: long = k * 13; m: long = k + 17; o: long = k * 19; q: long = k ^ 23;
    u: long = k * 29; w: long = k + 31; x: long = k ^ 37; y: long = k * 41;
    sp: long = 0;
    dp: long = 0;
    unsafe { sp = &b.s as long + 3; dp = &b.d as long + 5; }
    bad: long = 0;
    reset(b); unsafe { memcpy(dp, sp, 3); } if (!same(b, 3)) { bad = bad + 1; }
    reset(b); unsafe { memcpy(dp, sp, 5); } if (!same(b, 5)) { bad = bad + 2; }
    reset(b); unsafe { memcpy(dp, sp, 12); } if (!same(b, 12)) { bad = bad + 4; }
    reset(b); unsafe { memcpy(dp, sp, 40); } if (!same(b, 40)) { bad = bad + 8; }
    if (bad != 0) { return 200 + bad; }
    return a + c + e + f + g + h + j + m + o + q + u + w + x + y;
}

// Values a loop with a call in it keeps outnumber the registers a call leaves alone, and the
// loop reads them often, so the two addresses, read once after it, live in the frame: both
// scratch registers take an address and the bytes go through `xmm15`, or, under four bytes,
// the copy is `rep movsb`.
spilled b:&Bufs k:long -> long {
    sp: long = 0;
    dp: long = 0;
    unsafe { sp = &b.s as long + 3; dp = &b.d as long + 5; }
    a: long = k; c: long = k + 1; e: long = k + 2; f: long = k + 3; g: long = k + 4; h: long = k + 5; j: long = k + 6;
    for i in 0..k { a = a + i; c = c ^ a; e = e + c; f = f * 3 + e; g = g + f; h = h ^ g; j = j + h; reset(b); }
    bad: long = 0;
    unsafe { memcpy(dp, sp, 5); } if (!same(b, 5)) { bad = bad + 1; }
    reset(b); unsafe { memcpy(dp, sp, 3); } if (!same(b, 3)) { bad = bad + 2; }
    reset(b); unsafe { memcpy(dp, sp, 20); } if (!same(b, 20)) { bad = bad + 4; }
    if (bad != 0) { return 0 - bad; }
    return a + c + e + f + g + h + j;
}

main -> int {
    z: [u8; 160];
    for i in 0..160 { z[i] = 0; }
    b: Bufs = Bufs { s: z, d: z };
    r: long = lengths(&b);
    if (r != 0) { return r as int; }
    k: long = gK;
    got: long = crowded(&b, k);
    want: long = (k + 1) + k * 3 + (k ^ 5) + (k + 11) + k * 7 + (k - 2) + k * 13 + (k + 17) + k * 19
               + (k ^ 23) + k * 29 + (k + 31) + (k ^ 37) + k * 41;
    if (got != want) { return 250; }
    sf: fn(&Bufs, long) -> long = &spilled;
    if (sf(&b, k) < 0) { return 251; }
    return 0;
}
