// What the scaler leaves, rewritten before the emitter (`Opt.foldLate`), and a conversion that
// keeps every bit taken for a copy (`retargetCopies`):
// - a conversion stored only at its own width goes, the store taking its operand
//   (`narrowStores`); one also read at its full width stays;
// - a constant added to an address is folded into the accesses through it (`foldOffsets`);
// - a shift by a constant before a product by a constant is folded into the constant
//   (`shiftMuls`);
// - a `u32` load widened to `u64` is loaded straight into the wider value, both sides of a
//   comparison.
// ir-lacks: late_folds::store32 convert
// ir-has: late_folds::both convert
// ir-lacks: late_folds::copy16 , #8
// ir-has: late_folds::copy16 + 8]
// ir-lacks: late_folds::prev , #16
// ir-has: late_folds::prev + -16]
// ir-lacks: late_folds::hash shl
// ir-lacks: late_folds::widen convert
// ir-lacks: late_folds::same32 convert

var gSpin: long = 0;

same32 a:[u32] b:[u32] i:long j:long -> long {
    n: long = 0;
    for k in 0..i {
        if ((a[k] as u64) == (b[j - k] as u64)) { n = n + 1; }
    }
    return n;
}

store32 inout h:[u32] i:long n:long -> void {
    for k in 0..(i & 1) + 1 { gSpin = gSpin ^ k; }
    h[i] = (n * 3) as u32;
}
both inout h:[u32] i:long n:long -> long {
    for k in 0..(i & 1) + 1 { gSpin = gSpin ^ k; }
    c: u32 = (n * 3) as u32;
    h[i] = c;
    return c as long;
}
unsafe copy16 d:long s:long -> void {
    for k in 0..(d & 1) + 1 { gSpin = gSpin ^ k; }
    *(d as *u64) = *(s as *u64);
    *((d + 8) as *u64) = *((s + 8) as *u64);
}
// Below the address it is handed, by a constant taken away.
unsafe prev p:long -> long {
    for k in 0..(p & 1) + 1 { gSpin = gSpin ^ k; }
    return *((p - 16) as *long) * 10 + *((p - 8) as *long);
}
hash x:u64 -> long {
    for k in 0..((x & 1) as long) + 1 { gSpin = gSpin ^ k; }
    return (((x << 24) * 889523592379) >> 52) as long;
}
widen h:[u32] i:long -> long {
    for k in 0..(i & 1) + 1 { gSpin = gSpin ^ k; }
    return (h[i] as long) * 5;
}

// None of these may be rewritten. A conversion whose operand is written again before the store:
// the store takes the value converted. A narrowing then widened again: not a copy. An address
// sum whose base is written again before the access through it. A shifted value read twice.
later inout h:[u32] i:long n0:long -> long {
    n: long = n0;
    for k in 0..(i & 1) + 1 { gSpin = gSpin ^ k; }
    c: u32 = n as u32;
    n = n + 7;
    h[i] = c;
    return n;
}
narrowRet x:long -> long {
    for k in 0..(x & 1) + 1 { gSpin = gSpin ^ k; }
    return ((x * 300) as u8) as long;
}
unsafe moved p0:long -> long {
    p: long = p0;
    for k in 0..(p & 1) + 1 { gSpin = gSpin ^ k; }
    q: long = p + 8;
    p = p + 16;
    return *(q as *long) * 100 + *(p as *long);
}
twice x:u64 -> long {
    for k in 0..((x & 1) as long) + 1 { gSpin = gSpin ^ k; }
    s: u64 = x << 24;
    return ((s * 889523592379) ^ s) as long;
}

main -> int {
    h: [u32; 4];
    for i in 0..4 { h[i] = 0; }
    store32(&h, 1, -1);
    store32(&h, 2, 7);
    if (h[1] != 4294967293 || h[2] != 21) { return 1; }
    if (both(&h, 3, 1431655766) != 2 || both(&h, 0, -5) != 4294967281 || h[3] != 2) { return 2; }
    a: [long; 4] = [1, 2, 3, 4];
    b: [long; 4] = [0, 0, 0, 0];
    unsafe {
        copy16((&b[0] as *long) as long, (&a[1] as *long) as long);
        copy16((&b[2] as *long) as long, (&a[0] as *long) as long);
    }
    if (b[0] != 2 || b[1] != 3 || b[2] != 1 || b[3] != 2) { return 3; }
    h1: long = hash(12345678901);
    h2: long = hash((0 - 1) as u64);
    if (h1 != 3903) { return 4; }
    if (h2 != 782) { return 6; }
    if (widen(h[..], 0) != 21474836405 || widen(h[..], 2) != 105) { return 5; }
    c: [u32; 4] = [4294967281, 21, 7, 2];
    if (same32(h[..], c[..], 4, 3) != 1 || same32(c[..], c[..], 3, 2) != 1) { return 7; }
    if (later(&h, 1, 4294967301) != 4294967308 || h[1] != 5 || later(&h, 2, 9) != 16 || h[2] != 9) { return 8; }
    if (narrowRet(5) != 220 || narrowRet(1) != 44) { return 9; }
    m: long = 0;
    unsafe { m = moved((&a[0] as *long) as long); }
    if (m != 203) { return 10; }
    unsafe { m = prev((&a[3] as *long) as long); }
    if (m != 23) { return 13; }
    t1: long = twice(12345678901);
    t2: long = twice(3);
    if (t1 != -1070679982583316480) { return 11; }
    if (t2 != 7877700191912984576) { return 12; }
    return 0;
}
