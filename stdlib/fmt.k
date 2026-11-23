// Formatting: a format string, a list of arguments, and any `Write` sink.
//
// `writeTo(w, "x={}", n)` is an ordinary variadic call. The compiler collects the trailing
// arguments into a `[any]` slice of 24-byte {tag, x, y} boxes; the format bytes are walked here at
// runtime, literal runs written in chunks and each hole filled from the next box. A hole may carry
// a spec, `{:[[fill]align][+][#][0][width][.prec][type]}`; plain `{}` skips the spec parser
// entirely.
//
// This is the whole formatter, and it knows nothing about where the bytes go. `io` puts a default
// sink under it (`print`/`println` are `writeArgs` aimed at a locked, buffered stdout), and
// `string`'s `format` aims the same machinery at a growable buffer.
//
// It depends on `write` and nothing else: `io` includes this, so anything this included would be
// compiled into every program that prints. That is why `format` lives with the String it builds.
#include <write>

// ─── rendering a value into a scratch buffer ────────────────────────────────

// Decimal digits of |v|, no sign; returns the count. Works in the non-positive domain, so the
// most negative long, whose magnitude has no positive representation, still formats.
//
// The count comes first, from comparing with powers of ten (a multiply a digit, where dividing
// would cost far more), and then the digits go in right to left two at a time: one division by
// 100 gives a pair, read out of DIGIT_PAIRS. That halves the divisions and makes formatting a
// number two to two and a half times faster than a digit per `% 10` and `/ 10`.
//
// The compiler cannot prove right-to-left writes stay in range, so the highest index is checked
// once, through the slice, and the rest are written through the pointer: every later index is
// smaller than one already proved in range. One check per number instead of one per digit.
local DIGIT_PAIRS: str = "00010203040506070809101112131415161718192021222324252627282930313233343536373839404142434445464748495051525354555657585960616263646566676869707172737475767778798081828384858687888990919293949596979899";

local fmtDecMag v:long inout b:[u8] -> long {
    n: long = v;
    if (n > 0) { n = -n; }
    digits: long = 1;
    p: long = -10;
    while (digits < 19 && n <= p) { digits += 1; p *= 10; }     // a long has at most 19
    b[digits - 1] = '0' as u8;                                  // checked: the highest index
    unsafe {
        d: *u8 = b.ptr as *u8;
        pairs: *u8 = DIGIT_PAIRS.ptr as *u8;
        i: long = digits;
        while (n <= -100) {
            q: long = n / 100;
            r: long = 2 * (q * 100 - n);                        // the low two digits, 0..99, doubled
            i -= 2;
            d[i] = pairs[r];
            d[i + 1] = pairs[r + 1];
            n = q;
        }
        if (n <= -10) { d[0] = pairs[-2 * n]; d[1] = pairs[-2 * n + 1]; }
        else { d[0] = ('0' - n) as u8; }
    }
    return digits;
}
// The same digits for a value with no sign bit. Separate from fmtDecMag because that one
// works in the negative domain to reach the most-negative long, where a u64 past long's range
// is a different number and would print as one.
pkg fmtDecMagU v:u64 inout b:[u8] -> long {
    n: u64 = v;
    digits: long = 1;
    p: u64 = 10;
    while (digits < 20 && n >= p) { digits += 1; p *= 10; }     // a u64 has at most 20
    b[digits - 1] = '0' as u8;                                  // checked: the highest index
    unsafe {
        d: *u8 = b.ptr as *u8;
        pairs: *u8 = DIGIT_PAIRS.ptr as *u8;
        i: long = digits;
        while (n >= 100) {
            q: u64 = n / 100;
            r: long = (2 * (n - q * 100)) as long;
            i -= 2;
            d[i] = pairs[r];
            d[i + 1] = pairs[r + 1];
            n = q;
        }
        if (n >= 10) { r: long = (2 * n) as long; d[0] = pairs[r]; d[1] = pairs[r + 1]; }
        else { d[0] = (('0' as u64) + n) as u8; }
    }
    return digits;
}
pkg fmtDec v:long inout b:[u8] -> long {
    used: long = 0;
    if (v < 0) { b[0] = '-' as u8; used = 1; }
    return used + fmtDecMag(v, &b[used..]);
}

// Unsigned base 2^bits (hex 4, octal 3, binary 1). The value is a u64, so `>>` fills with zeros
// and a high-bit value prints its raw two's-complement pattern, like Rust's `{:x}`.
local fmtRadix v:u64 bits:long upper:bool inout b:[u8] -> long {
    mask: u64 = ((1 << bits) - 1) as u64;
    digits: long = 1;
    t: u64 = v >> bits;
    while (t != 0) { digits = digits + 1; t = t >> bits; }
    n: u64 = v;
    i: long = digits;
    b[i - 1] = 0;                                               // checked: the highest index
    unsafe {
        p: *u8 = b.ptr as *u8;
        while (i > 0) {
            i -= 1;
            d: long = (n & mask) as long;
            ch: long = '0' + d;
            if (d > 9) { if (upper) { ch = 'A' + d - 10; } else { ch = 'a' + d - 10; } }
            p[i] = ch as u8;
            n >>= bits;
        }
    }
    return digits;
}

// ─── put*: one primitive into a sink ────────────────────────────────────────
// The most bytes a number can print as, in decimal: -9223372036854775808 and
// 18446744073709551615 are 20, -2147483648 is 11. Shared with `string`'s pushLong/pushULong.
pkg LONG_TEXT_MAX: long = 20;
local INT_TEXT_MAX: long = 11;

pub putInt w:Write v:long -> void {
    scratch: [u8; INT_TEXT_MAX];
    n: long = fmtDec(v, &scratch[..]);
    putStr(w, scratch[..n] as str);
}
pub putLong w:Write v:long -> void {
    scratch: [u8; LONG_TEXT_MAX];
    n: long = fmtDec(v, &scratch[..]);
    putStr(w, scratch[..n] as str);
}
pub putULong w:Write v:u64 -> void {
    scratch: [u8; LONG_TEXT_MAX];
    n: long = fmtDecMagU(v, &scratch[..]);
    putStr(w, scratch[..n] as str);
}
// Lowercase hex, no prefix or leading zeros: what `{:x}` prints.
pub putHex w:Write v:u64 -> void {
    scratch: [u8; 16];
    n: long = fmtRadix(v, 4, false, &scratch[..]);
    putStr(w, scratch[..n] as str);
}
pub putChar w:Write c:long -> void {
    scratch: [u8; 1];
    scratch[0] = c as u8;
    putStr(w, scratch[..] as str);
}
// Safe: a `str` carries its own length, so nothing trusts the caller for a bound.
pub putStr w:Write s:str -> void {
    unsafe { w.write(s.ptr, s.len); }
}
// The raw form. `unsafe`: the caller supplies both the address and the length and nothing
// checks them.
pub unsafe putBytes w:Write ptr:long len:long -> void {
    w.write(ptr, len);
}
pub putF64 w:Write x:f64 -> void {
    bits: long = 0;
    unsafe { asm { in rax x; out bits rax; } }
    putFloatBits(w, bits, false);
}
pub putF32 w:Write x:f32 -> void {
    bits: long = 0;
    unsafe { asm { in rax x; out bits rax; } }        // sign-extended, as a box holds it
    putFloatBits(w, bits, true);
}

// ─── floats ─────────────────────────────────────────────────────────────────
// A float prints as decimal digits computed exactly, on big integers, so every digit is the true
// one: `{}` the fewest that read back as the same float (Steele & White's free-format method, in
// Burger & Dybvig's form), `{:.N}` and `{:.Ne}` the value rounded to N places, ties to even. It
// works on the bits, as a box carries them: an f64's 64, an f32's 32 sign-extended.

// A non-negative integer in 32-bit limbs, least significant first. Nothing the digit loops build
// passes 2^1100 (an f64 near its top, times 2 * 10; 2^1076 below its bottom), so the limbs are a
// fixed array and formatting a float allocates nothing. Declared, never built with a literal or
// copied whole: those are unrolled, a store per limb.
local struct Big { n: long, d: [long; 36] }

local bigSet inout b:Big v:long -> void {                     // v >= 0
    b.n = 0;
    x: long = v;
    while (x != 0) { b.d[b.n] = x & 0xFFFF_FFFF; b.n = b.n + 1; x = x >> 32; }
}
local bigCopy inout to:Big from:Big -> void {
    for i in 0..from.n { to.d[i] = from.d[i]; }
    to.n = from.n;
}
// b * m + a, for m and a below 2^31.
local bigMulAdd inout b:Big m:long a:long -> void {
    carry: long = a;
    for i in 0..b.n {
        v: long = b.d[i] * m + carry;
        b.d[i] = v & 0xFFFF_FFFF;
        carry = v >> 32;
    }
    if (carry != 0) { b.d[b.n] = carry; b.n = b.n + 1; }
}
local bigMulPow10 inout b:Big k:long -> void {
    left: long = k;
    while (left >= 9) { bigMulAdd(b, 1000000000, 0); left = left - 9; }
    m: long = 1;
    for i in 0..left { m = m * 10; }
    if (m > 1) { bigMulAdd(b, m, 0); }
}
local bigShl inout b:Big k:long -> void {
    if (b.n == 0) { return; }
    words: long = k / 32;
    bits: long = k % 32;
    if (bits > 0) {
        carry: long = 0;
        for i in 0..b.n {
            v: long = (b.d[i] << bits) | carry;
            b.d[i] = v & 0xFFFF_FFFF;
            carry = v >> 32;
        }
        if (carry != 0) { b.d[b.n] = carry; b.n = b.n + 1; }
    }
    if (words > 0) {
        i: long = b.n - 1;
        while (i >= 0) { b.d[i + words] = b.d[i]; i = i - 1; }
        for j in 0..words { b.d[j] = 0; }
        b.n += words;
    }
}
local bigAdd inout a:Big b:Big -> void {
    n: long = a.n;
    if (b.n > n) { n = b.n; }
    carry: long = 0;
    for i in 0..n {
        v: long = carry;
        if (i < a.n) { v = v + a.d[i]; }
        if (i < b.n) { v = v + b.d[i]; }
        a.d[i] = v & 0xFFFF_FFFF;
        carry = v >> 32;
    }
    a.n = n;
    if (carry != 0) { a.d[n] = carry; a.n = n + 1; }
}
// a - b, for a >= b.
local bigSub inout a:Big b:Big -> void {
    borrow: long = 0;
    for i in 0..a.n {
        v: long = a.d[i] - borrow;
        if (i < b.n) { v = v - b.d[i]; }
        if (v < 0) { v = v + 0x1_0000_0000; borrow = 1; } else { borrow = 0; }
        a.d[i] = v;
    }
    while (a.n > 0 && a.d[a.n - 1] == 0) { a.n = a.n - 1; }
}
local bigCmp a:Big b:Big -> long {
    if (a.n != b.n) { if (a.n < b.n) { return -1; } return 1; }
    i: long = a.n - 1;
    while (i >= 0) {
        if (a.d[i] != b.d[i]) { if (a.d[i] < b.d[i]) { return -1; } return 1; }
        i -= 1;
    }
    return 0;
}
// The sign of (a + b) - c, `t` the scratch for the sum.
local bigSumCmp a:Big b:Big c:Big inout t:Big -> long {
    bigCopy(t, a);
    bigAdd(t, b);
    return bigCmp(t, c);
}

// A float's decimal digits: the value is 0.d[0]d[1]...d[n-1] * 10^k, and no digits is a zero.
// An f64 written out exactly has at most 767 significant digits, so the array holds any of them.
local struct Digits { d: [u8; 800], n: long, k: long }

local pushDigit inout out:Digits v:long -> void {
    out.d[out.n] = ('0' + v) as u8;
    out.n += 1;
}
// One more in the last place: 0.1299 becomes 0.1300, and 0.999 becomes 0.100 a place up.
local roundUp inout out:Digits -> void {
    i: long = out.n - 1;
    while (i >= 0 && out.d[i] == '9') { out.d[i] = '0' as u8; i = i - 1; }
    if (i >= 0) { out.d[i] = (out.d[i] + 1) as u8; return; }
    if (out.n == 0) { out.n = 1; }
    out.d[0] = '1' as u8;
    out.k += 1;
}

// Is (r + m) / s at or past 1, `even` making the boundary itself count?
local pastOne r:Big m:Big s:Big even:bool inout t:Big -> bool {
    c: long = bigSumCmp(r, m, s, t);
    return c > 0 || (c == 0 && even);
}

// The digits of f * 2^e (f > 0, a `p`-bit significand, `minE` the subnormals' exponent): when
// `prec` < 0 the fewest that read back as this float, else the value rounded to `prec` places
// after the point (`fixed`) or after the first digit.
local genDigits f:long e:long p:long minE:long fixed:bool prec:long inout out:Digits -> void {
    shortest: bool = prec < 0;
    even: bool = (f & 1) == 0;            // reading back, a tie goes to the even significand
    // The value is r / s. For the shortest digits, mp / s and mm / s are the distances to halfway
    // to the next float up and down; they differ only at a power of two, where the gap below is
    // half the gap above. Everything is doubled (quadrupled there) to keep the halves whole.
    u: long = 0;
    if (shortest && f == (1 << (p - 1)) && e > minE) { u = 1; }
    r: Big;
    s: Big;
    mp: Big;
    mm: Big;
    t: Big;                               // scratch
    t.n = 0;
    r.n = 0;
    s.n = 0;
    mp.n = 0;
    mm.n = 0;
    bigSet(&r, f);
    bigSet(&s, 1);
    bigSet(&mp, 1);
    bigSet(&mm, 1);
    if (shortest) { bigShl(&r, 1 + u); bigShl(&s, 1 + u); bigShl(&mp, u); }
    if (e >= 0) { bigShl(&r, e); bigShl(&mp, e); bigShl(&mm, e); }
    else { bigShl(&s, 0 - e); }

    // Scale so that r / s is in [0.1, 1) and the value is that times 10^k. k first from the
    // binary exponent (78913 / 2^18 is just under log10 2), then corrected by a place either way.
    bitLen: long = 0;
    rest: long = f;
    while (rest != 0) { bitLen = bitLen + 1; rest = rest >> 1; }
    k: long = (((e + bitLen - 1) * 78913) >> 18) + 1;
    if (k >= 0) { bigMulPow10(&s, k); }
    else { bigMulPow10(&r, 0 - k); bigMulPow10(&mp, 0 - k); bigMulPow10(&mm, 0 - k); }
    if (shortest) {
        // Here the upper halfway point is what has to stay below 1.
        while (pastOne(r, mp, s, even, &t)) { bigMulAdd(&s, 10, 0); k = k + 1; }
        while (true) {
            bigCopy(&t, r);
            bigAdd(&t, mp);
            bigMulAdd(&t, 10, 0);
            c: long = bigCmp(t, s);
            if (c > 0 || (c == 0 && even)) { break; }
            bigMulAdd(&r, 10, 0); bigMulAdd(&mp, 10, 0); bigMulAdd(&mm, 10, 0);
            k -= 1;
        }
    } else {
        while (bigCmp(r, s) >= 0) { bigMulAdd(&s, 10, 0); k = k + 1; }
        while (true) {
            bigCopy(&t, r);
            bigMulAdd(&t, 10, 0);
            if (bigCmp(t, s) >= 0) { break; }
            bigMulAdd(&r, 10, 0);
            k -= 1;
        }
    }
    out.n = 0;
    out.k = k;

    if (shortest) {
        // Digit by digit, stopping at the first that leaves the value inside its halfway points:
        // rounding it down (`low`) or up (`high`) then reads back as this float.
        while (true) {
            bigMulAdd(&r, 10, 0); bigMulAdd(&mp, 10, 0); bigMulAdd(&mm, 10, 0);
            dg: long = 0;
            while (bigCmp(r, s) >= 0) { bigSub(&r, s); dg = dg + 1; }
            cl: long = bigCmp(r, mm);
            low: bool = cl < 0 || (cl == 0 && even);
            high: bool = pastOne(r, mp, s, even, &t);
            pushDigit(out, dg);
            if (!low && !high) { continue; }
            up: bool = high;
            if (low && high) {                // both read back: the nearer, a tie to even
                c: long = bigSumCmp(r, r, s, &t);
                up = c > 0 || (c == 0 && (dg & 1) == 1);
            }
            if (up) { roundUp(out); }
            while (out.n > 1 && out.d[out.n - 1] == '0') { out.n = out.n - 1; }
            return;
        }
    }
    want: long = prec + 1;
    if (fixed) { want = k + prec; }
    if (want < 0) { out.k = 0; return; }        // under a tenth of the last place: zero
    while (out.n < want && r.n > 0 && out.n < 800) {
        bigMulAdd(&r, 10, 0);
        dg: long = 0;
        while (bigCmp(r, s) >= 0) { bigSub(&r, s); dg = dg + 1; }
        pushDigit(out, dg);
    }
    if (out.n == want && r.n > 0) {             // what is left decides the last place, a tie to even
        c: long = bigSumCmp(r, r, s, &t);
        odd: bool = out.n > 0 && (out.d[out.n - 1] & 1) == 1;
        if (c > 0 || (c == 0 && odd)) { roundUp(out); }
    }
    if (out.n == 0) { out.k = 0; }
}

local enum FloatClass { Finite, Infinite, Nan }

local classOf bits:long single:bool -> FloatClass {
    top: long = (bits >> 52) & 0x7FF;
    frac: long = bits & 0xF_FFFF_FFFF_FFFF;
    if (single) { top = (bits >> 23) & 0xFF; frac = bits & 0x7F_FFFF; }
    if ((single && top != 0xFF) || (!single && top != 0x7FF)) { return FloatClass.Finite; }
    if (frac == 0) { return FloatClass.Infinite; }
    return FloatClass.Nan;
}

// A finite float's digits, its sign aside.
local floatDigits bits:long single:bool fixed:bool prec:long inout out:Digits -> void {
    frac: long = bits & 0xF_FFFF_FFFF_FFFF;
    ex: long = (bits >> 52) & 0x7FF;
    p: long = 53;
    bias: long = 1075;                    // so that the value is significand * 2^(ex - bias)
    if (single) { frac = bits & 0x7F_FFFF; ex = (bits >> 23) & 0xFF; p = 24; bias = 150; }
    out.n = 0;
    out.k = 0;
    if (ex != 0) { genDigits(frac | (1 << (p - 1)), ex - bias, p, 1 - bias, fixed, prec, out); }
    else if (frac != 0) { genDigits(frac, 1 - bias, p, 1 - bias, fixed, prec, out); }   // subnormal
}

// The digits at places from..to of 0.d0d1d2..., a zero at any place outside them.
local putPlaces w:Write dg:Digits from:long to:long -> void {
    j: long = from;
    if (j < 0) {
        z: long = to;
        if (z > 0) { z = 0; }
        padFill(w, '0', z - j);
        j = z;
    }
    end: long = to;
    if (end > dg.n) { end = dg.n; }
    if (j < end) { putStr(w, dg.d[j..end] as str); j = end; }
    padFill(w, '0', to - j);
}

// A finite float with no sign. `{}`: the shortest digits, plain from 1e-4 to below 1e16 and in
// exponent form outside that; `{:.N}`: N places after the point; `{:e}`, `{:.Ne}`: exponent form,
// `ech` its letter.
local floatBody w:Write dg:Digits sci:bool prec:long ech:long -> void {
    if (dg.n == 0) {
        if (!sci && prec < 0) { putStr(w, "0.0"); return; }
        putChar(w, '0');
        if (prec > 0) { putChar(w, '.'); padFill(w, '0', prec); }
        if (sci) { putChar(w, ech); putChar(w, '0'); }
        return;
    }
    x: long = dg.k - 1;                   // the exponent of d.ddd
    if (sci || (prec < 0 && (x < -4 || x >= 16))) {
        putPlaces(w, dg, 0, 1);
        last: long = dg.n;
        if (prec >= 0) { last = prec + 1; }
        if (last > 1) { putChar(w, '.'); putPlaces(w, dg, 1, last); }
        putChar(w, ech);
        putLong(w, x);
    }
    else if (prec >= 0) {
        if (dg.k <= 0) { putChar(w, '0'); } else { putPlaces(w, dg, 0, dg.k); }
        if (prec > 0) { putChar(w, '.'); putPlaces(w, dg, dg.k, dg.k + prec); }
    }
    else if (dg.k <= 0) { putStr(w, "0."); putPlaces(w, dg, dg.k, dg.n); }
    else if (dg.k < dg.n) { putPlaces(w, dg, 0, dg.k); putChar(w, '.'); putPlaces(w, dg, dg.k, dg.n); }
    else { putPlaces(w, dg, 0, dg.k); putStr(w, ".0"); }
}

local floatOrWord w:Write cls:FloatClass dg:Digits sci:bool prec:long ech:long -> void {
    if (cls == FloatClass.Nan) { putStr(w, "NaN"); }
    else if (cls == FloatClass.Infinite) { putStr(w, "inf"); }
    else { floatBody(w, dg, sci, prec, ech); }
}


// ─── format specifiers ──────────────────────────────────────────────────────
// `{:[[fill]align][+][#][0][width][.prec][type]}`: fill+align `< > ^`, forced sign `+`,
// alternate form `#` (0x/0b/0o), zero-pad `0`, minimum `width`, and `.prec`, which truncates
// strings and rounds floats. The type is one of `x X b o d c s p e E`. `e` prints a float in
// exponent form, and `x` and the other radix types print a float's raw bits.

// How a field's spare width is distributed. `Unset` means no alignment was written, so the
// zero-pad flag and the per-kind default can both check for it.
local enum Align { Unset, Left, Right, Center }

// What the body being laid out actually is, once an explicit type and the box tag have both
// had their say.
local enum Kind { Decimal, Radix, Text, Char, Shown }

local struct FmtSpec {
    fill: long, align: Align, sign: bool, alt: bool,
    zero: bool, width: long, prec: long, ty: long
}

// One byte of the format string, or 0 past its end, so the parser can look ahead freely.
local byteAt f:[u8] k:long -> long { if (k < f.len) { return f[k]; } return 0; }
local isAlign c:long -> bool { return c == '<' || c == '>' || c == '^'; }
local alignOf c:long -> Align {
    if (c == '<') { return Align.Left; }
    if (c == '^') { return Align.Center; }
    return Align.Right;
}
local isDigitByte c:long -> bool { return c >= '0' && c <= '9'; }
local isRadixByte c:long -> bool { return c == 'x' || c == 'X' || c == 'b' || c == 'o' || c == 'p'; }
local isTypeByte c:long -> bool {
    return isRadixByte(c) || c == 'd' || c == 'c' || c == 's' || c == 'e' || c == 'E';
}

// The text between `{:` and `}`, on its own. The caller has already found the closing brace,
// so this parses a self-contained slice from 0 and keeps no position of its own.
local parseSpec f:[u8] -> FmtSpec {
    s: FmtSpec = FmtSpec { fill: ' ', align: Align.Unset, sign: false, alt: false, zero: false, width: 0, prec: -1, ty: 0 };
    j: long = 0;
    c0: long = byteAt(f, j);
    c1: long = byteAt(f, j + 1);
    if (isAlign(c1)) { s.fill = c0; s.align = alignOf(c1); j = j + 2; }        // [fill]align
    else if (isAlign(c0)) { s.align = alignOf(c0); j = j + 1; }
    if (byteAt(f, j) == '+') { s.sign = true; j = j + 1; }
    else if (byteAt(f, j) == '-') { j = j + 1; }                  // accepted, ignored
    if (byteAt(f, j) == '#') { s.alt = true; j = j + 1; }
    if (byteAt(f, j) == '0') { s.zero = true; j = j + 1; }
    while (isDigitByte(byteAt(f, j))) {                           // width
        s.width = s.width * 10 + (byteAt(f, j) - '0'); j = j + 1;
    }
    if (byteAt(f, j) == '.') {                                    // precision
        j = j + 1; s.prec = 0;
        while (isDigitByte(byteAt(f, j))) {
            s.prec = s.prec * 10 + (byteAt(f, j) - '0'); j = j + 1;
        }
    }
    tc: long = byteAt(f, j);
    if (isTypeByte(tc)) { s.ty = tc; }
    return s;
}

// `n` copies of `ch`, chunked so a wide pad is a few writes rather than n.
local padFill w:Write ch:long n:long -> void {
    if (n <= 0) { return; }
    scratch: [u8; 32];
    for k in 0..32 { scratch[k] = ch as u8; }
    left: long = n;
    while (left > 0) {
        c: long = left; if (c > 32) { c = 32; }
        putStr(w, scratch[..c] as str);
        left -= c;
    }
}

// A sink that keeps nothing and counts what it was given: how wide a `Display` value renders,
// asked before padding it.
local struct CountWriter { n: long }
methods CountWriter for Write {
    write &self ptr:long len:long -> long { self.n = self.n + len; return len; }
}

// ─── the argument boxes ─────────────────────────────────────────────────────
// The compiler's `any`: 24 bytes per variadic argument. Reading one through a `*AnyBox` names
// the three words instead of counting offsets, and `boxes + i` steps a whole box because
// pointer arithmetic scales by the pointee.
local struct AnyBox { tag: long, x: long, y: long }

// The tag values the compiler stamps. `Str` puts ptr in x and len in y; `Display` puts &data in
// x and &vtable in y; the rest carry a value in x.
local enum BoxTag: long { Int, Long, Str, Display, Char, ULong, F64, F32, Bool }

// Call a Display value's `display(&self, sink)` (slot 0 of its vtable) so it renders into the
// same sink, recursively.
local unsafe callDisplay w:Write data:long vtable:long -> void {
    slot: *long = vtable as *long;
    method: fn(long, Write)->void = slot[0] as fn(long, Write)->void;
    method(data, w);
}

// Render one box under a parsed spec: build the body, work out the sign and 0x-style prefix,
// then lay it out to `width` with fill and alignment.
local unsafe emitSpec w:Write e:*AnyBox s:FmtSpec -> void {
    tag: long = e.tag;
    x: long = e.x;
    ty: long = s.ty;
    if ((tag == BoxTag.F64 || tag == BoxTag.F32) && !isRadixByte(ty)) { callFloat(w, e, &s as long); return; }
    if (tag == BoxTag.Bool && ty == 0) { if (x != 0) { putStr(w, "true"); } else { putStr(w, "false"); } return; }

    // An explicit type wins; otherwise the box tag decides.
    kind: Kind = Kind.Decimal;
    if (tag == BoxTag.Display) { kind = Kind.Shown; }
    else if (ty == 0) {
        if (tag == BoxTag.Str) { kind = Kind.Text; }
        else if (tag == BoxTag.Char) { kind = Kind.Char; }
    }
    else if (ty == 's') { kind = Kind.Text; }
    else if (ty == 'c') { kind = Kind.Char; }
    else if (isRadixByte(ty)) { kind = Kind.Radix; }

    body: [u8; 80];
    view: [u8] = body[..0];        // the rendered body: a slice of `body`, or of the argument
    signCh: long = 0;
    pre0: long = 0;
    pre1: long = 0;
    isNum: bool = false;
    shownLen: long = 0;            // a Display value's width, measured rather than rendered here

    if (kind == Kind.Shown) {
        if (s.width > 0) { counter: CountWriter = CountWriter { n: 0 }; callDisplay(counter, x, e.y); shownLen = counter.n; }
    }
    else if (kind == Kind.Text) {
        view = (x as *u8)[..e.y];                            // the box's own bytes
        if (s.prec >= 0 && view.len > s.prec) { view = view[..s.prec]; }
    }
    else if (kind == Kind.Char) {
        body[0] = x as u8;
        view = body[..1];
    }
    else if (kind == Kind.Radix) {
        isNum = true;
        v: u64 = x as u64;
        if (tag == BoxTag.Int || tag == BoxTag.F32) { v = v & (0xFFFFFFFF as u64); }   // an int is its low 32 bits; a ULong is all 64
        n: long = 0;
        if (ty == 'b') { n = fmtRadix(v, 1, false, &body[..]); }
        else if (ty == 'o') { n = fmtRadix(v, 3, false, &body[..]); }
        else { n = fmtRadix(v, 4, ty == 'X', &body[..]); }                 // x / X / p
        view = body[..n];
        if (s.alt || ty == 'p') {                            // pointers always get 0x
            pre0 = '0';
            if (ty == 'b') { pre1 = 'b'; } else if (ty == 'o') { pre1 = 'o'; }
            else if (ty == 'X') { pre1 = 'X'; } else { pre1 = 'x'; }
        }
    }
    else if (tag == BoxTag.ULong) {
        isNum = true;
        if (s.sign) { signCh = '+'; }
        view = body[..fmtDecMagU(x as u64, &body[..])];      // no sign bit: 2^63 is a magnitude
    }
    else {
        isNum = true;
        if (x < 0) { signCh = '-'; }
        else if (s.sign) { signCh = '+'; }
        view = body[..fmtDecMag(x, &body[..])];              // the sign is emitted separately
    }

    after: long = layHead(w, s, isNum, signCh, pre0, pre1, view.len + shownLen);
    if (kind == Kind.Shown) { callDisplay(w, x, e.y); } else { putStr(w, view as str); }
    padFill(w, s.fill, after);
}

// The part of a field ahead of its body: the fill when it is aligned right or centred, the sign,
// the 0x-style prefix, and a zero-padded number's zeros. Answers the fill still owed after it.
local layHead w:Write s:FmtSpec isNum:bool signCh:long pre0:long pre1:long bodyLen:long -> long {
    headLen: long = 0;
    if (signCh != 0) { headLen = headLen + 1; }
    if (pre0 != 0) { headLen = headLen + 1; }
    if (pre1 != 0) { headLen = headLen + 1; }
    pad: long = s.width - (headLen + bodyLen);
    if (pad < 0) { pad = 0; }

    // The '0' flag zero-pads a number whose alignment was not written: sign, prefix, zeros, body.
    zeroPad: bool = s.zero && isNum && s.align == Align.Unset;
    align: Align = s.align;
    if (align == Align.Unset) {                              // numbers right, text left
        if (isNum) { align = Align.Right; } else { align = Align.Left; }
    }
    before: long = 0;                                        // fill ahead of the head; the rest goes after
    if (!zeroPad) {
        if (align == Align.Right) { before = pad; }
        else if (align == Align.Center) { before = pad / 2; }
    }
    padFill(w, s.fill, before);
    if (signCh != 0) { putChar(w, signCh); }
    if (pre0 != 0) { putChar(w, pre0); }
    if (pre1 != 0) { putChar(w, pre1); }
    if (zeroPad) { padFill(w, '0', pad); before = pad; }
    return pad - before;
}

// `{}`: the shortest digits.
local putFloatBits w:Write bits:long single:bool -> void {
    plain: FmtSpec = FmtSpec { fill: ' ', align: Align.Unset, sign: false, alt: false, zero: false, width: 0, prec: -1, ty: 0 };
    emitFloatSpec(w, bits, single, plain);
}
// A float under a spec: the body measured first when there is a width to lay it out in. A NaN
// has no sign, anything else negative (-0.0 too) has a '-', and an infinity or a NaN is never
// zero-padded.
local emitFloatSpec w:Write bits:long single:bool s:FmtSpec -> void {
    cls: FloatClass = classOf(bits, single);
    sci: bool = s.ty == 'e' || s.ty == 'E';
    ech: long = 'e';
    if (s.ty == 'E') { ech = 'E'; }
    dg: Digits;
    dg.n = 0;
    dg.k = 0;
    if (cls == FloatClass.Finite) { floatDigits(bits, single, !sci, s.prec, &dg); }
    signCh: long = 0;
    if (cls != FloatClass.Nan) { if (bits < 0) { signCh = '-'; } else if (s.sign) { signCh = '+'; } }
    sp: FmtSpec = s;
    if (cls != FloatClass.Finite) { sp.zero = false; }
    bodyLen: long = 0;
    if (s.width > 0) {
        counter: CountWriter = CountWriter { n: 0 };
        floatOrWord(counter, cls, dg, sci, s.prec, ech);
        bodyLen = counter.n;
    }
    after: long = layHead(w, sp, true, signCh, 0, 0, bodyLen);
    floatOrWord(w, cls, dg, sci, s.prec, ech);
    padFill(w, s.fill, after);
}

// A float box carries the formatter's address in `y` (the compiler puts `floatBoxFormat` there),
// so a program that never boxes a float never reaches, and never links, the float formatter.
local unsafe callFloat w:Write e:*AnyBox spec:long -> void {
    if (e.y == 0) { putStr(w, "<float>"); return; }
    f: fn(Write, long, long)->void = e.y as fn(Write, long, long)->void;
    f(w, e as long, spec);
}
// What a float box's `y` names: the box's own address and a `*FmtSpec` (0 for a plain `{}`).
pub floatBoxFormat w:Write box:long spec:long -> void {
    unsafe {
        e: *AnyBox = box as *AnyBox;
        single: bool = e.tag == BoxTag.F32;
        if (spec == 0) { putFloatBits(w, e.x, single); }
        else { sp: *FmtSpec = spec as *FmtSpec; emitFloatSpec(w, e.x, single, *sp); }
    }
}

// ─── the format interpreter ─────────────────────────────────────────────────
local unsafe emitArg w:Write e:*AnyBox -> void {
    tag: long = e.tag;
    if (tag == BoxTag.Int) { putInt(w, e.x); }
    else if (tag == BoxTag.Long) { putLong(w, e.x); }
    else if (tag == BoxTag.ULong) { putULong(w, e.x as u64); }
    else if (tag == BoxTag.Str) { putBytes(w, e.x, e.y); }
    else if (tag == BoxTag.Char) { putChar(w, e.x); }
    else if (tag == BoxTag.F64 || tag == BoxTag.F32) { callFloat(w, e, 0); }
    else if (tag == BoxTag.Bool) { if (e.x != 0) { putStr(w, "true"); } else { putStr(w, "false"); } }
    else { callDisplay(w, e.x, e.y); }
}

// `args` is a plain `[any]` slice rather than variadic, so a caller can forward its own
// variadic slice straight through.
local unsafe emitFmt w:Write fmt:str args:[any] -> void {
    f: [u8] = fmt as [u8];
    boxes: *AnyBox = args.ptr as *AnyBox;
    argc: long = args.len;
    i: long = 0;          // position in the format bytes
    a: long = 0;          // next argument to consume
    runStart: long = 0;   // start of the current literal run
    while (i < f.len) {
        c: long = f[i];
        if (c == '{' || c == '}') {                            // flush the pending run first
            if (i > runStart) { putStr(w, f[runStart..i] as str); }
            next: long = byteAt(f, i + 1);
            if (c == '{') {
                if (next == '}') {                             // {}: the fast path
                    if (a < argc) { emitArg(w, boxes + a); a = a + 1; }
                    i += 2;
                }
                else if (next == '{') { putChar(w, '{'); i = i + 2; }
                else if (next == ':') {                        // {: … }
                    end: long = i + 2;                         // the spec runs to the closing brace
                    while (end < f.len && f[end] != '}') { end = end + 1; }
                    sp: FmtSpec = parseSpec(f[i + 2..end]);
                    if (a < argc) { emitSpec(w, boxes + a, sp); a = a + 1; }
                    i = end + 1;                               // past the '}', or past the end
                }
                else { putChar(w, '{'); i = i + 1; }
            }
            else {
                if (next == '}') { putChar(w, '}'); i = i + 2; }
                else { putChar(w, '}'); i = i + 1; }
            }
            runStart = i;
        }
        else { i = i + 1; }
    }
    if (i > runStart) { putStr(w, f[runStart..i] as str); }
}

// ─── the public surface ─────────────────────────────────────────────────────
pub writeTo w:Write fmt:str rest:...any -> void {
    unsafe { emitFmt(w, fmt, rest); }
}
// The same formatter, taking an argument list that has already been collected. A function with a
// `...any` tail of its own cannot forward it to `writeTo`: passing a `[any]` to a variadic makes
// it one argument, and the formatter then refuses to print a slice. So a forwarder calls this.
pub writeArgs w:Write fmt:str args:[any] -> void {
    unsafe { emitFmt(w, fmt, args); }
}
