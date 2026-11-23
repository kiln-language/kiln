// A `memcpy` of a constant length up to 128 bytes is moves, not `rep movsb` (`emitShortCopy`):
// twelve bytes are a word at 0 and a word at 4, the second ending where the copy ends. Past 128
// bytes, and for a length not known, it is `rep movsb`.
// asm-lacks: short_memcpy::copy12 rep movsb
// asm-has: short_memcpy::copy12 + 4]
// asm-has: short_memcpy::copy200 rep movsb
// asm-has: short_memcpy::copyN rep movsb
pub unsafe builtin memcpy dst:long src:long n:long -> void;
copy12 d:long s:long -> void { unsafe { memcpy(d, s, 12); } }
copy200 d:long s:long -> void { unsafe { memcpy(d, s, 200); } }
copyN d:long s:long n:long -> void { unsafe { memcpy(d, s, n); } }
main -> int {
    a: [u8; 256];
    b: [u8; 256];
    for i in 0..256 { a[i] = i as u8; b[i] = 0; }
    f: fn(long, long) -> void = &copy12;
    g: fn(long, long) -> void = &copy200;
    h: fn(long, long, long) -> void = &copyN;
    unsafe {
        f(&b as long, &a as long);
        if (b[11] != 11 || b[12] != 0) { return 1; }
        g(&b as long, &a as long);
        if (b[199] != 199 || b[200] != 0) { return 2; }
        h(&b as long, &a as long, 220);
        if (b[219] != 219 || b[220] != 0) { return 3; }
    }
    return 0;
}
