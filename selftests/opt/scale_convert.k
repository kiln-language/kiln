// A word read through `(p + i) as *long` is one access, `[p + i]`: the sum and the conversion
// that made it an address go (`Scaler.fold`).
// asm-lacks: scale_convert::wordAt lea
wordAt p:long i:long -> long {
    r: long = 0;
    unsafe { r = *((p + i) as *long); }
    return r;
}
main -> int {
    a: [long; 4] = [5, 6, 7, 8];
    f: fn(long, long) -> long = &wordAt;
    unsafe {
        if (f(&a as long, 16) != 7) { return 1; }
    }
    return 0;
}
