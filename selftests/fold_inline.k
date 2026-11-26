#include <stdlib::{string, bytes}>

// Calls copied for what their constant arguments leave of the callee (`Relayout.foldTarget`):
// `startsWith`, `endsWith` and `bytesEqual` on literals of every length the callee's paths
// tell apart (none, short, four to seven, eight and past), matching and not, in loops, against
// the same answers worked out a byte at a time. A literal with an escape in it is read back
// byte for byte as the assembler writes it (`--no-literal-bytes`), and `s[s.len - n..]`'s length
// is `n` (`a - (a - b)`, `--no-reassociate`).

local byHand s:str t:str at:long -> bool {
    if (at < 0 || at + t.len > s.len) { return false; }
    for i in 0..t.len {
        if ((s as [u8])[at + i] != (t as [u8])[i]) { return false; }
    }
    return true;
}

// With `n` 3, the second test of the first `if` jumps over the target of the `||`, which the
// first test still reaches: the jump it is decided to take must stay a jump in the copy. The
// second `if` decides the filler away, which is what leaves the copy small.
local route k:long n:long -> long {
    r: long = 0;
    if (k > 0 || n != 3) { r = k * 3 + 1; } else { r = k - 5; }
    if (n != 3) {
        r = r * 7 + k; r = r ^ (k << 3); r = r + (k >> 2); r = r * 5 - k; r = r ^ (r >> 7);
        r = r + k * k; r = r - (k & 255); r = r * 3 + 11; r = r ^ (k << 5); r = r + (r >> 3);
    }
    return r;
}

// A branch on `(x ^ y) == 0` is one on `x == y` (`xorTest`).
local sameBits x:long y:long -> long {
    if ((x ^ y) == 0) { return 1; }
    return 2;
}

// The view's length is `s.len - (s.len - 3)`, read in one block: 3.
local tail3 s:str -> bool { return bytesEqual((s as [u8])[s.len - 3..], "ded" as [u8]); }

// An unsigned comparison with a constant past the signed range: the largest `u64` is not below 16.
local bucket n:u64 -> long {
    r: long = 0;
    if (n < 16) { r = 1; } else { r = 2; }
    if (n == 7) {
        r = r * 7 + 3; r = r ^ (r << 3); r = r + (r >> 2); r = r * 5 - 1; r = r ^ (r >> 7);
        r = r + r * r; r = r - (r & 255); r = r * 3 + 11; r = r ^ (r << 5); r = r + (r >> 3);
    }
    return r;
}

main -> int {
    texts: [str; 6] = ["key=value;tag=appended", "kez=value", "", "ab\tcd\nef", "abcdefghijklmnop", "lang"];
    bad: long = 0;
    hits: long = 0;
    for r in 0..3 {
        for k in 0..6 {
            s: str = texts[k];
            a: bool = strStartsWith(s, "key=");
            if (a != byHand(s, "key=", 0)) { bad = bad + 1; }
            b: bool = strEndsWith(s, "lang");
            if (b != byHand(s, "lang", s.len - 4)) { bad = bad + 1; }
            c: bool = strStartsWith(s, "ab\tcd\n");
            if (c != byHand(s, "ab\tcd\n", 0)) { bad = bad + 1; }
            d: bool = strEndsWith(s, "ijklmnop");
            if (d != byHand(s, "ijklmnop", s.len - 8)) { bad = bad + 1; }
            e: bool = strStartsWith(s, "");
            if (!e) { bad = bad + 1; }
            f: bool = strStartsWith(s, "k");
            if (f != byHand(s, "k", 0)) { bad = bad + 1; }
            g: bool = strEndsWith(s, "abcdefghijklmnop");
            if (g != byHand(s, "abcdefghijklmnop", s.len - 16)) { bad = bad + 1; }
            j: bool = strStartsWith(s, "key");
            if (j != byHand(s, "key", 0)) { bad = bad + 1; }
            m: bool = strEndsWith(s, "ded");
            if (m != byHand(s, "ded", s.len - 3)) { bad = bad + 1; }
            if (s.len >= 3) {
                q: bool = bytesEqual((s as [u8])[s.len - 3..], "ded" as [u8]);
                if (q != m || tail3(s) != m) { bad = bad + 1; }
            }
            h: bool = bytesEqual(s as [u8], "kez=value" as [u8]);
            if (h != (s.len == 9 && byHand(s, "kez=value", 0))) { bad = bad + 1; }
            if (a) { hits = hits + 1; }
            if (b) { hits = hits + 2; }
            if (c) { hits = hits + 4; }
            if (d) { hits = hits + 8; }
            if (g) { hits = hits + 16; }
            if (h) { hits = hits + 32; }
        }
    }
    big: u64 = 18446744073709551615;
    for k in 0..3 {
        if (bucket(18446744073709551615) != 2 || bucket(big) != 2) { bad = bad + 1; }
    }
    sb: fn(long, long) -> long = &sameBits;
    for k in 0..6 {
        want: long = 2;
        if (k == 3) { want = 1; }
        if (sb(k, 3) != want) { bad = bad + 1; }
    }
    rf: fn(long, long) -> long = &route;
    for k in 0 - 4..5 {
        if (route(k, 3) != rf(k, 3)) { bad = bad + 1; }
    }
    if (bad != 0) { return 1; }
    if (hits != 3 * (1 + 2 + 4 + 8 + 16 + 32)) { return 2; }
    return 0;
}
