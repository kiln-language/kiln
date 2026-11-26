// A function taking a `str` or a slice is copied into its callers like any other small body: the
// parameter's slot only ever held the caller's address, so it is a temp (`promoteLocals`), and the
// splice reads the caller's pair where it lies. A string literal's length read out of its pair is
// the constant, and a byte read out of it at a known offset is that byte (`--no-literal-bytes`),
// so `first("z")` is 122 with no address of the bytes left.
// ir-lacks: main call
// ir-lacks: main strlit
// ir-has: main const 3
// ir-lacks: main straddr
lenOf xs:[long] -> long { return xs.len; }
firstOf xs:[long] -> long { return xs[0]; }
slen s:str -> long { return s.len; }
first s:str -> long { return s[0] as long; }
main -> int {
    v: [long; 3] = [5, 2, 3];
    if (lenOf(v[..]) != 3 || firstOf(v[..]) != 5 || slen("abc") != 3 || first("z") != 122) { return 1; }
    return 0;
}
