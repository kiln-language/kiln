// Floating point: what Rust's f64 and f32 have as methods, without the transcendental functions
// (exp, ln, sin, ...), which want a libm this library does not have yet.
//
//     r: f64 = x.sqrt();   x.floor();   x.abs();   x.min(y);   x.isNan();   x.toBits();
//     f64.fromBits(b);     f64.parse("1.5e-3")          // Option<f64>
//     sortBy(&v, TotalOrder { });                       // floats have no Ord
//
// A float has neither `Ord` nor `Hash`, as in Rust: `<` is IEEE's partial order (a NaN is
// unordered), and `==` holds between -0.0 and 0.0, whose bits differ, and fails between a NaN and
// itself, so no hash could agree with it. `totalCmp` orders the bits, for sorting; a map keyed by
// a float keys by its `toBits()`.
//
// Printing (`{}`, `{:.3}`, `{:e}`) is in fmt; `Encode`/`Decode` are in encode.
#include <{core, cmp, fmt, option, vec, chars}>

pub INFINITY: f64 = 1.0 / 0.0;
pub NAN: f64 = -(0.0 / 0.0);          // 0.0 / 0.0 is x86's NaN, sign bit set; Rust's NAN has it clear
pub PI: f64 = 3.141592653589793;

// The bits as a long. An f64's sign is bit 63; with it cleared, an infinity is exactly INF64 and a
// NaN anything above. An f32's are its 32 sign-extended, the way the compiler keeps them, and the
// same tests hold with INF32.
local bits64 x:f64 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local of64 b:long -> f64 { r: f64 = 0.0; unsafe { asm { in rax b; out r rax; } } return r; }
local bits32 x:f32 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local of32 b:long -> f32 { r: f32 = 0.0; unsafe { asm { in rax b; "movsxd rax, eax" out r rax; } } return r; }

local MAG64: long = 0x7FFF_FFFF_FFFF_FFFF;
local INF64: long = 0x7FF0_0000_0000_0000;
local MAG32: long = 0x7FFF_FFFF;
local INF32: long = 0x7F80_0000;

methods f64 {
    toBits &self -> u64 { return bits64(self) as u64; }
    fromBits b:u64 -> f64 { return of64(b as long); }
    parse s:str -> Option<f64> {
        b: Option<long> = parseBits(s, false);
        match b { Some(v) { return Option.Some(of64(v)); } None { return Option.None; } }
    }

    isNan &self -> bool { return self != self; }
    isInfinite &self -> bool { return (bits64(self) & MAG64) == INF64; }
    isFinite &self -> bool { return (bits64(self) & MAG64) < INF64; }
    isSignNegative &self -> bool { return bits64(self) < 0; }

    abs &self -> f64 { return of64(bits64(self) & MAG64); }
    copySign &self sign:f64 -> f64 { return of64((bits64(self) & MAG64) | (bits64(sign) & ~MAG64)); }
    sqrt &self -> f64 {
        r: f64 = 0.0;
        unsafe { asm { in rax self; "movq xmm0, rax" "sqrtsd xmm0, xmm0" "movq rax, xmm0" out r rax; } }
        return r;
    }

    // Toward zero. From 2^52 up every f64 is whole already, and an infinity or a NaN is kept.
    trunc &self -> f64 {
        if (!(self.abs() < 4503599627370496.0)) { return self; }
        return ((self as long) as f64).copySign(self);
    }
    floor &self -> f64 { t: f64 = self.trunc(); if (t > self) { return t - 1.0; } return t; }
    ceil &self -> f64 { t: f64 = self.trunc(); if (t < self) { return t + 1.0; } return t; }
    // The nearest whole number, halfway cases away from zero (C's `round`).
    round &self -> f64 {
        t: f64 = self.trunc();
        d: f64 = self - t;                        // exact
        if (d >= 0.5) { return t + 1.0; }
        if (d <= -0.5) { return t - 1.0; }
        return t;
    }
    fract &self -> f64 { return self - self.trunc(); }

    // The smaller and the larger. A NaN loses to any number (IEEE's minNum and maxNum), and -0.0
    // counts as below 0.0.
    min &self other:f64 -> f64 {
        if (self < other) { return self; }
        if (other < self || self.isNan()) { return other; }
        if (other.isNan() || self.isSignNegative()) { return self; }
        return other;
    }
    max &self other:f64 -> f64 {
        if (self > other) { return self; }
        if (other > self || self.isNan()) { return other; }
        if (other.isNan() || !self.isSignNegative()) { return self; }
        return other;
    }
    // Held to lo..=hi; a NaN stays a NaN.
    clamp &self lo:f64 hi:f64 -> f64 {
        if (self < lo) { return lo; }
        if (self > hi) { return hi; }
        return self;
    }
    // self^n, by squaring: a rounding per step, so not always the nearest float.
    powi &self n:long -> f64 {
        k: u64 = n as u64;
        if (n < 0) { k = (0 - n) as u64; }        // long's minimum comes out as 2^63, right
        r: f64 = 1.0;
        b: f64 = self;
        while (k != 0) {
            if ((k & 1) != 0) { r = r * b; }
            b = b * b;
            k = k >> 1;
        }
        if (n < 0) { return 1.0 / r; }
        return r;
    }

    // IEEE's totalOrder: -NaN < -inf < ... < -0.0 < 0.0 < ... < inf < NaN. A negative's bits order
    // backwards, so its magnitude bits are flipped first.
    totalCmp &self other:f64 -> int {
        a: long = bits64(self);
        b: long = bits64(other);
        if (a < 0) { a = a ^ MAG64; }
        if (b < 0) { b = b ^ MAG64; }
        return a.cmp(b);
    }
}

methods f32 {
    toBits &self -> u32 { return (bits32(self) & 0xFFFF_FFFF) as u32; }
    fromBits b:u32 -> f32 { return of32(b as long); }
    parse s:str -> Option<f32> {
        b: Option<long> = parseBits(s, true);
        match b { Some(v) { return Option.Some(of32(v)); } None { return Option.None; } }
    }

    isNan &self -> bool { return self != self; }
    isInfinite &self -> bool { return (bits32(self) & MAG32) == INF32; }
    isFinite &self -> bool { return (bits32(self) & MAG32) < INF32; }
    isSignNegative &self -> bool { return bits32(self) < 0; }

    abs &self -> f32 { return of32(bits32(self) & MAG32); }
    copySign &self sign:f32 -> f32 { return of32((bits32(self) & MAG32) | (bits32(sign) & ~MAG32)); }
    sqrt &self -> f32 {
        r: f32 = 0.0;
        unsafe { asm { in rax self; "movd xmm0, eax" "sqrtss xmm0, xmm0" "movd eax, xmm0" "movsxd rax, eax" out r rax; } }
        return r;
    }

    // Through f64, which holds every f32 exactly and every result here too.
    trunc &self -> f32 { return (self as f64).trunc() as f32; }
    floor &self -> f32 { return (self as f64).floor() as f32; }
    ceil &self -> f32 { return (self as f64).ceil() as f32; }
    round &self -> f32 { return (self as f64).round() as f32; }
    fract &self -> f32 { return (self as f64).fract() as f32; }
    min &self other:f32 -> f32 { return (self as f64).min(other as f64) as f32; }
    max &self other:f32 -> f32 { return (self as f64).max(other as f64) as f32; }
    clamp &self lo:f32 hi:f32 -> f32 {
        if (self < lo) { return lo; }
        if (self > hi) { return hi; }
        return self;
    }
    // Computed in f64 and rounded once at the end.
    powi &self n:long -> f32 { return (self as f64).powi(n) as f32; }
    totalCmp &self other:f32 -> int {
        a: long = bits32(self);
        b: long = bits32(other);
        if (a < 0) { a = a ^ MAG32; }
        if (b < 0) { b = b ^ MAG32; }
        return a.cmp(b);
    }
}

methods f64 for Display { display &self w:Write -> void { putF64(w, self); } }
methods f32 for Display { display &self w:Write -> void { putF32(w, self); } }

// `totalCmp` as a comparator: `sortBy(&v, TotalOrder { })`.
pub struct TotalOrder { }
methods TotalOrder for Compare<f64> { compare &self a:f64 b:f64 -> int { return a.totalCmp(b); } }
methods TotalOrder for Compare<f32> { compare &self a:f32 b:f32 -> int { return a.totalCmp(b); } }

// ─── parsing ─────────────────────────────────────────────────────────────────
// `[+-]digits[.digits][(e|E)[+-]digits]`, where either side of the point may be empty but not
// both, or `inf`, `infinity` or `nan` in any case, signed or not; nothing else, no spaces. The
// value is the nearest float, ties to even, the way the compiler reads a literal.

local byteAt b:[u8] i:long -> long { if (i < b.len) { return b[i]; } return 0; }
// `b` is `word` (lowercase), in any case.
local isWord b:[u8] word:str -> bool {
    w: [u8] = word as [u8];
    if (b.len != w.len) { return false; }
    for i in 0..b.len {
        c: long = b[i];
        if (c >= 'A' && c <= 'Z') { c = c + 32; }
        if (c != w[i]) { return false; }
    }
    return true;
}
local infBits single:bool -> long { if (single) { return INF32; } return INF64; }
local nanBits single:bool -> long {
    if (single) { return 0x7FC0_0000; }
    return 0x7FF8_0000_0000_0000;
}

local parseBits s:str single:bool -> Option<long> {
    b: [u8] = s as [u8];
    at: long = 0;
    sign: long = 0;
    if (byteAt(b, 0) == '+' || byteAt(b, 0) == '-') {
        at = 1;
        if (b[0] == '-') { sign = 0 - 9223372036854775807 - 1; if (single) { sign = 0 - 2147483648; } }
    }
    num: [u8] = b[at..];
    if (isWord(num, "inf") || isWord(num, "infinity")) { return Option.Some(sign | infBits(single)); }
    if (isWord(num, "nan")) { return Option.Some(sign | nanBits(single)); }

    // Check the form, and gather what the quick path needs: the significant digits as a number m
    // (while they fit) and the power of ten that scales it.
    m: long = 0;
    sig: long = 0;
    scale: long = 0;
    any: bool = false;
    j: long = 0;
    while (isDigit(byteAt(num, j))) {
        c: long = num[j] - '0';
        any = true;
        if (sig > 0 || c != 0) {
            if (sig < 18) { m = m * 10 + c; } else { scale = scale + 1; }
            sig = sig + 1;
        }
        j = j + 1;
    }
    if (byteAt(num, j) == '.') {
        j = j + 1;
        while (isDigit(byteAt(num, j))) {
            c: long = num[j] - '0';
            any = true;
            if (sig > 0 || c != 0) {
                if (sig < 18) { m = m * 10 + c; scale = scale - 1; }
                sig = sig + 1;
            } else { scale = scale - 1; }
            j = j + 1;
        }
    }
    if (!any) { return Option.None; }
    if (byteAt(num, j) == 'e' || byteAt(num, j) == 'E') {
        j = j + 1;
        neg: bool = byteAt(num, j) == '-';
        if (neg || byteAt(num, j) == '+') { j = j + 1; }
        if (!isDigit(byteAt(num, j))) { return Option.None; }
        e: long = 0;
        while (isDigit(byteAt(num, j))) {
            if (e < 100000) { e = e * 10 + (num[j] - '0'); }
            j = j + 1;
        }
        if (neg) { scale = scale - e; } else { scale = scale + e; }
    }
    if (j != num.len) { return Option.None; }
    if (sig == 0) { return Option.Some(sign); }

    // Quick path (Clinger): m and 10^|scale| both exact in the format, so the one multiply or
    // divide is the only rounding, and IEEE makes that one the nearest.
    places: long = scale;
    if (places < 0) { places = 0 - places; }
    if (!single && sig <= 15 && places <= 22) {
        v: f64 = m as f64;
        p: f64 = 1.0;
        for k in 0..places { p = p * 10.0; }
        if (scale < 0) { v = v / p; } else { v = v * p; }
        return Option.Some(sign | bits64(v));
    }
    if (single && sig <= 7 && places <= 10) {
        v: f32 = m as f32;
        p: f32 = 1.0;
        for k in 0..places { p = p * 10.0; }
        if (scale < 0) { v = v / p; } else { v = v * p; }
        return Option.Some(sign | bits32(v));
    }
    return Option.Some(sign | exactBits(num, single));
}

// The nearest float to a well-formed unsigned decimal, exactly: its digits are a big integer D,
// the value D * 10^E, and the quotient (or product) is taken in whole numbers so that only the
// last step rounds. The compiler's `support::fp::decimalToFloat`, which reads literals, with a cap
// on the digits kept.
local exactBits text:[u8] single:bool -> long {
    d: Vec<long>;                 // the significant digits: 32-bit limbs, low first
    exp10: long = 0;
    seenDot: bool = false;
    kept: long = 0;
    sticky: bool = false;
    i: long = 0;
    while (i < text.len) {
        c: long = text[i];
        if (c == '.') { seenDot = true; i = i + 1; continue; }
        if (!isDigit(c)) { break; }
        if (kept > 0 || c != '0') {
            if (kept < 800) {
                bigMulAdd(&d, 10, c - '0');
                kept = kept + 1;
                if (seenDot) { exp10 = exp10 - 1; }
            } else {
                if (c != '0') { sticky = true; }
                if (!seenDot) { exp10 = exp10 + 1; }
            }
        } else if (seenDot) { exp10 = exp10 - 1; }
        i = i + 1;
    }
    // A value halfway between two floats has under 800 significant digits, so past them only
    // "more than nothing" matters, and one more nonzero digit says it.
    if (sticky) { bigMulAdd(&d, 10, 1); exp10 = exp10 - 1; }
    if (i < text.len) {                                   // the exponent: the form is checked
        i = i + 1;
        neg: bool = text[i] == '-';
        if (neg || text[i] == '+') { i = i + 1; }
        e: long = 0;
        while (i < text.len) {
            if (e < 100000) { e = e * 10 + (text[i] - '0'); }
            i = i + 1;
        }
        if (neg) { exp10 = exp10 - e; } else { exp10 = exp10 + e; }
    }
    p: long = 53;
    minExp: long = 0 - 1022;
    maxExp: long = 1023;
    if (single) { p = 24; minExp = 0 - 126; maxExp = 127; }
    if (bigIsZero(d)) { return 0; }
    // Far out of range either way: the big numbers below would only say so slowly.
    if (exp10 + bigDigits(d) > 400) { return infBits(single); }
    if (exp10 + bigDigits(d) < 0 - 400) { return 0; }

    // value = q * 2^(-k), q = D * 10^exp10 * 2^k in whole numbers: a negative exponent divides,
    // by 10^9 at a time, and k leaves the quotient at least p + 2 bits so the rounding bits are
    // real ones. 10^n has at most n * 3402 / 1024 + 1 bits (3402 / 1024 is just over log2 10);
    // a k too large only costs time.
    q: Vec<long> = d;
    places: long = 0;
    if (exp10 >= 0) { bigMulPow10(&q, exp10); } else { places = 0 - exp10; }
    k: long = p + 3 + places * 3402 / 1024 + 1 - bigBits(q);
    if (k < 0) { k = 0; }
    bigShl(&q, k);
    rem: bool = false;
    while (places > 0) {
        n: long = places;
        if (n > 9) { n = 9; }
        step: long = 1;
        for j in 0..n { step = step * 10; }
        if (bigDivSmall(&q, step)) { rem = true; }
        places = places - n;
    }
    L: long = bigBits(q);
    lead: long = L - 1 - k;                               // the binary exponent of the leading bit
    keepBits: long = p;                                   // fewer below the smallest normal exponent
    if (lead < minExp) { keepBits = p - (minExp - lead); }
    if (keepBits < 0) { return 0; }                       // under half the smallest subnormal
    drop: long = L - keepBits;
    m: long = 0;
    if (drop <= 0) { m = bigLow64(q) << (0 - drop); drop = 0; }
    else {
        m = bigShrLow64(q, drop);
        half: bool = bigBit(q, drop - 1);
        sticky2: bool = rem || bigAnyBelow(q, drop - 1);
        if (half && (sticky2 || (m & 1) != 0)) { m = m + 1; }
    }
    // Rounding up may carry into a new bit: one more of exponent.
    if (keepBits == p && m == (1 << p)) { m = m >> 1; lead = lead + 1; }
    if (keepBits < p && m == (1 << keepBits)) { lead = lead + 1; }   // a subnormal rounded up into a normal
    if (lead > maxExp) { return infBits(single); }
    if (lead < minExp || (keepBits < p && m < (1 << (p - 1)))) { return m; }   // subnormal
    bias: long = 1023;
    if (single) { bias = 127; }
    return ((lead + bias) << (p - 1)) | (m & ((1 << (p - 1)) - 1));
}

// ─── big integers: 32-bit limbs in a Vec<long>, least significant first ──────
// (fmt has its own, in a fixed array: printing must not allocate, and its numbers stay small.)

local bigMulAdd inout x:Vec<long> m:long a:long -> void {
    carry: long = a;
    for i in 0..x.len() {
        v: long = x.get(i) * m + carry;
        x.set(i, v & 4294967295);
        carry = v >> 32;
    }
    while (carry != 0) { x.push(carry & 4294967295); carry = carry >> 32; }
}
local bigMulPow10 inout x:Vec<long> n:long -> void {
    left: long = n;
    while (left >= 9) { bigMulAdd(x, 1000000000, 0); left = left - 9; }
    m: long = 1;
    for j in 0..left { m = m * 10; }
    if (m > 1) { bigMulAdd(x, m, 0); }
}
local bigIsZero x:Vec<long> -> bool {
    for v in x { if (v != 0) { return false; } }
    return true;
}
local bigBits x:Vec<long> -> long {
    i: long = x.len() - 1;
    while (i >= 0 && x.get(i) == 0) { i = i - 1; }
    if (i < 0) { return 0; }
    top: long = x.get(i);
    b: long = 0;
    while (top != 0) { top = top >> 1; b = b + 1; }
    return i * 32 + b;
}
// A rough decimal digit count, for the range test: bits * log10(2).
local bigDigits x:Vec<long> -> long { return bigBits(x) * 30103 / 100000 + 1; }
local bigShl inout x:Vec<long> k:long -> void {
    if (k <= 0) { return; }
    words: long = k / 32;
    bits: long = k % 32;
    if (bits > 0) {
        carry: long = 0;
        for i in 0..x.len() {
            v: long = (x.get(i) << bits) | carry;
            x.set(i, v & 4294967295);
            carry = v >> 32;
        }
        if (carry != 0) { x.push(carry); }
    }
    if (words > 0) {
        n: long = x.len();
        for j in 0..words { x.push(0); }
        i: long = n - 1;
        while (i >= 0) { x.set(i + words, x.get(i)); i = i - 1; }
        for j in 0..words { x.set(j, 0); }
    }
}
local bigBit x:Vec<long> b:long -> bool {
    if (b < 0) { return false; }
    w: long = b / 32;
    if (w >= x.len()) { return false; }
    return ((x.get(w) >> (b % 32)) & 1) != 0;
}
// Any bit set below bit `b`.
local bigAnyBelow x:Vec<long> b:long -> bool {
    if (b <= 0) { return false; }
    w: long = b / 32;
    for i in 0..w { if (i < x.len() && x.get(i) != 0) { return true; } }
    return w < x.len() && (x.get(w) & ((1 << (b % 32)) - 1)) != 0;
}
local bigLow64 x:Vec<long> -> long {
    v: long = 0;
    if (x.len() > 0) { v = x.get(0); }
    if (x.len() > 1) { v = v | (x.get(1) << 32); }
    return v;
}
// What is left of x shifted right by s, as many bits as fit.
local bigShrLow64 x:Vec<long> s:long -> long {
    v: long = 0;
    for b in 0..63 { if (bigBit(x, s + b)) { v = v | (1 << b); } }
    return v;
}
// x / d in place, for 0 < d < 2^31; answers whether a remainder was left.
local bigDivSmall inout x:Vec<long> d:long -> bool {
    r: long = 0;
    i: long = x.len() - 1;
    while (i >= 0) {
        cur: long = (r << 32) | x.get(i);
        x.set(i, cur / d);
        r = cur % d;
        i = i - 1;
    }
    return r != 0;
}
