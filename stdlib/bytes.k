// Hashing and comparing byte ranges — what a map hashing its keys and a string comparing its
// contents both need. Everything takes a `[u8]`, so nothing here is unsafe: a `str` becomes
// one with `s as [u8]`, which moves nothing.

// FNV-1a over the bytes, plus a final avalanche. Uses the 32-bit offset basis with the 64-bit
// prime, since the 64-bit basis does not fit in a signed long; the mix at the end makes up for
// the weaker spread in the high bits.
pub hashBytes b:[u8] -> long {
    h: long = 2166136261;
    for c in b { h = (h ^ c) * 1099511628211; }
    h = h ^ (h >> 29);          // `>>` is arithmetic here; callers mask to the low bits
    h = h * 1099511628211;
    return h ^ (h >> 32);
}

// Where the two first differ, or the shorter length if one is a prefix of the other.
pub commonPrefix x:[u8] y:[u8] -> long {
    n: long = x.len;
    if (y.len < n) { n = y.len; }
    for i in 0..n {
        if (x[i] != y[i]) { return i; }
    }
    return n;
}

// The same bytes?
pub bytesEqual x:[u8] y:[u8] -> bool {
    return x.len == y.len && commonPrefix(x, y) == x.len;
}

// Three-way, bytewise and unsigned, the way `memcmp` orders: negative, zero or positive. A
// proper prefix orders first.
pub bytesCompare x:[u8] y:[u8] -> int {
    i: long = commonPrefix(x, y);
    if (i < x.len && i < y.len) {
        if (x[i] < y[i]) { return -1; }
        return 1;
    }
    if (x.len < y.len) { return -1; }
    if (x.len > y.len) { return 1; }
    return 0;
}

// The first position at or after `from` holding `b`, or -1.
pub bytesIndexOf hay:[u8] b:u8 from:long -> long {
    start: long = from;
    if (start < 0) { start = 0; }
    for i in start..hay.len {
        if (hay[i] == b) { return i; }
    }
    return -1;
}
