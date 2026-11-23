// Hashing and comparing byte ranges, which a map hashing its keys and a string comparing its
// contents both need. Everything takes a `[u8]`, so nothing here is unsafe: a `str` becomes
// one with `s as [u8]`, which moves nothing. The comparisons and the byte search read eight
// bytes at a time through the slice's own pointer, never outside it; x86 does not mind the
// unaligned loads.
#include <cmp>

// Eight bytes a step: each word is scrambled (multiply, xorshift, multiply, as MurmurHash64A
// does) and folded in with one more multiply, and the length goes in first so "a" and "a\0"
// land apart. The last 1 to 7 bytes become one more word through loads that stay inside the
// slice: the final eight shifted down, or for a short string two overlapping halves, or its
// first, middle and last byte. `mixHash` finishes, the same avalanche every scalar key gets, so
// the low bits a table masks down to depend on every byte.
//
// Byte at a time FNV-1a did this before; on the compiler's own identifiers and on paths it
// fills a 3/4-full table just as evenly (build/try/bytes/hq.k) and is 1.8 to 3.5 times faster.
local WORD_MUL: u64 = 0xC6A4A7935BD1E995;
local scrambleWord w:u64 -> u64 {
    k: u64 = w * WORD_MUL;
    k ^= k >> 47;
    return k * WORD_MUL;
}
pub hashBytes b:[u8] -> long {
    n: long = b.len;
    h: u64 = (n as u64) * WORD_MUL;
    unsafe {
        p: long = b.ptr as long;
        i: long = 0;
        while (i + 8 <= n) {
            h = (h ^ scrambleWord(*((p + i) as *u64))) * WORD_MUL;
            i += 8;
        }
        r: long = n - i;
        if (r > 0) {
            t: u64 = 0;
            if (n >= 8) { t = *((p + n - 8) as *u64) >> ((8 - r) * 8); }
            else if (r >= 4) { t = (*(p as *u32) as u64) | ((*((p + n - 4) as *u32) as u64) << 32); }
            else { t = (*(p as *u8) as u64) | ((*((p + r / 2) as *u8) as u64) << 8) | ((*((p + n - 1) as *u8) as u64) << 16); }
            h = (h ^ scrambleWord(t)) * WORD_MUL;
        }
    }
    return mixHash(h) as long;
}

// Where the two first differ, or the shorter length if one is a prefix of the other. Equal
// words are skipped eight bytes at a time; the bytes then pin down where they differ.
pub commonPrefix x:[u8] y:[u8] -> long {
    n: long = x.len;
    if (y.len < n) { n = y.len; }
    i: long = 0;
    unsafe {
        a: long = x.ptr as long;
        b: long = y.ptr as long;
        while (i + 8 <= n && *((a + i) as *u64) == *((b + i) as *u64)) { i += 8; }
        while (i < n && *((a + i) as *u8) == *((b + i) as *u8)) { i += 1; }
    }
    return i;
}

// The same bytes? From eight bytes up, whole words and then the last eight again (overlapping
// the one before, which is cheaper than a byte loop for the tail). Four to seven bytes are two
// overlapping four-byte loads XORed together and tested once, and only the shortest go a byte
// at a time.
pub bytesEqual x:[u8] y:[u8] -> bool {
    n: long = x.len;
    if (y.len != n) { return false; }
    unsafe {
        a: long = x.ptr as long;
        b: long = y.ptr as long;
        if (n >= 8) {
            i: long = 0;
            while (i + 8 < n) {
                if (*((a + i) as *u64) != *((b + i) as *u64)) { return false; }
                i += 8;
            }
            return *((a + n - 8) as *u64) == *((b + n - 8) as *u64);
        }
        if (n >= 4) {
            return ((*(a as *u32) ^ *(b as *u32)) | (*((a + n - 4) as *u32) ^ *((b + n - 4) as *u32))) == 0;
        }
        for i in 0..n {
            if (*((a + i) as *u8) != *((b + i) as *u8)) { return false; }
        }
    }
    return true;
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

// The first position at or after `from` holding `b`, or -1. Eight bytes a step: XOR with `b`
// in every byte turns each match into a zero byte, and `(w - 0x01..01) & ~w & 0x80..80` is
// nonzero exactly when `w` has one. Its lowest set bit is in the first zero byte (a borrow can
// only mark bytes above a real zero), and multiplying that byte's bit into 0x0001020304050607
// leaves the byte's index in the top eight bits.
pub bytesIndexOf hay:[u8] b:u8 from:long -> long {
    i: long = from;
    if (i < 0) { i = 0; }
    n: long = hay.len;
    unsafe {
        p: long = hay.ptr as long;
        pat: u64 = (b as u64) * 0x0101010101010101;
        while (i + 8 <= n) {
            w: u64 = *((p + i) as *u64) ^ pat;
            z: u64 = (w - 0x0101010101010101) & ~w & 0x8080808080808080;
            if (z != 0) {
                bit: u64 = (z & (~z + 1)) >> 7;
                return i + ((bit * 0x0001020304050607) >> 56) as long;
            }
            i += 8;
        }
        while (i < n) {
            if (*((p + i) as *u8) == b) { return i; }
            i += 1;
        }
    }
    return -1;
}
