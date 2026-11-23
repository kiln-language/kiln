// Floating point, as the compiler computes it: on bit patterns held in a `long`.
//
// The compiler's own source cannot use a float type until a seed reads one, so the evaluator and
// the constant folder do their float arithmetic here, on the bits, with the SSE instructions the
// emitted code uses (`asm`). That is what keeps a value folded at compile time bit-identical to
// the one the program would have computed: the same instruction, the same rounding mode
// (round-to-nearest-even, which nothing changes), no reassociation.
//
// An `f64` is its 64 bits. An `f32` is its 32 bits sign-extended, the canonical form the emitter
// keeps every 4-byte signed value in (`movsxd`), so two equal `f32`s are two equal `long`s.
//
// Also here: decimal literal text to the nearest `f64` or `f32`, correctly rounded, in integer
// arithmetic on big numbers (no float is involved, so nothing double-rounds).
#include <stdlib::{chars, string, vec}>

pub F64_SIGN: long = 0 - 9223372036854775807 - 1;
pub F32_SIGN: long = 0 - 2147483648;          // bit 31, sign-extended as an f32 is kept

// An f32's 32 bits as the compiler keeps them: sign-extended.
pub canonF32 v:long -> long { return (v << 32) >> 32; }

// ─── arithmetic ──────────────────────────────────────────────────────────────

// `a op b` for op 0 add, 1 subtract, 2 multiply, 3 divide.
pub f64Arith op:long a:long b:long -> long {
    r: long = 0;
    if (op == 0) {
        unsafe { asm { in rax a; in rdx b; "movq xmm0, rax" "movq xmm1, rdx" "addsd xmm0, xmm1" "movq rax, xmm0" out r rax; } }
    } else if (op == 1) {
        unsafe { asm { in rax a; in rdx b; "movq xmm0, rax" "movq xmm1, rdx" "subsd xmm0, xmm1" "movq rax, xmm0" out r rax; } }
    } else if (op == 2) {
        unsafe { asm { in rax a; in rdx b; "movq xmm0, rax" "movq xmm1, rdx" "mulsd xmm0, xmm1" "movq rax, xmm0" out r rax; } }
    } else {
        unsafe { asm { in rax a; in rdx b; "movq xmm0, rax" "movq xmm1, rdx" "divsd xmm0, xmm1" "movq rax, xmm0" out r rax; } }
    }
    return r;
}

pub f32Arith op:long a:long b:long -> long {
    r: long = 0;
    if (op == 0) {
        unsafe { asm { in rax a; in rdx b; "movd xmm0, eax" "movd xmm1, edx" "addss xmm0, xmm1" "movd eax, xmm0" out r rax; } }
    } else if (op == 1) {
        unsafe { asm { in rax a; in rdx b; "movd xmm0, eax" "movd xmm1, edx" "subss xmm0, xmm1" "movd eax, xmm0" out r rax; } }
    } else if (op == 2) {
        unsafe { asm { in rax a; in rdx b; "movd xmm0, eax" "movd xmm1, edx" "mulss xmm0, xmm1" "movd eax, xmm0" out r rax; } }
    } else {
        unsafe { asm { in rax a; in rdx b; "movd xmm0, eax" "movd xmm1, edx" "divss xmm0, xmm1" "movd eax, xmm0" out r rax; } }
    }
    return canonF32(r);
}

// The flags `ucomisd`/`ucomiss` leave, as bits: 1 unordered (PF), 2 below (CF), 4 equal (ZF).
local f64Flags a:long b:long -> long {
    r: long = 0;
    unsafe { asm {
        in rax a;
        in rdx b;
        "movq xmm0, rax"
        "movq xmm1, rdx"
        "xor eax, eax"
        "xor edx, edx"
        "ucomisd xmm0, xmm1"
        "setp al"
        "setb dl"
        "lea rax, [rax + rdx*2]"
        "mov edx, 0"
        "sete dl"
        "lea rax, [rax + rdx*4]"
        out r rax;
    } }
    return r;
}

local f32Flags a:long b:long -> long {
    r: long = 0;
    unsafe { asm {
        in rax a;
        in rdx b;
        "movd xmm0, eax"
        "movd xmm1, edx"
        "xor eax, eax"
        "xor edx, edx"
        "ucomiss xmm0, xmm1"
        "setp al"
        "setb dl"
        "lea rax, [rax + rdx*2]"
        "mov edx, 0"
        "sete dl"
        "lea rax, [rax + rdx*4]"
        out r rax;
    } }
    return r;
}

// `a op b`, op one of 0 ==, 1 !=, 2 <, 3 <=, 4 >, 5 >=, as IEEE says: a NaN on either side makes
// every comparison false except `!=`, which is true.
pub fpCompare op:long a:long b:long single:bool -> bool {
    f: long = 0;
    if (single) { f = f32Flags(a, b); } else { f = f64Flags(a, b); }
    if ((f & 1) != 0) { return op == 1; }          // unordered
    lt: bool = (f & 2) != 0;
    eq: bool = (f & 4) != 0;
    if (op == 0) { return eq; }
    if (op == 1) { return !eq; }
    if (op == 2) { return lt; }
    if (op == 3) { return lt || eq; }
    if (op == 4) { return !lt && !eq; }
    return !lt;
}

// ─── conversions ─────────────────────────────────────────────────────────────

// A signed 64-bit integer to the nearest f64 / f32.
pub i64ToF64 v:long -> long {
    r: long = 0;
    unsafe { asm { in rax v; "cvtsi2sd xmm0, rax" "movq rax, xmm0" out r rax; } }
    return r;
}
pub i64ToF32 v:long -> long {
    r: long = 0;
    unsafe { asm { in rax v; "cvtsi2ss xmm0, rax" "movd eax, xmm0" out r rax; } }
    return canonF32(r);
}

// An unsigned 64-bit integer to the nearest f64 / f32. With the top bit clear this is the signed
// conversion. With it set, the value is halved (keeping the low bit as a sticky bit, so the
// rounding comes out the same), converted as signed, and doubled.
pub u64ToF64 v:long -> long {
    if (v >= 0) { return i64ToF64(v); }
    h: long = ((v as u64) >> (1 as u64)) as long;
    h = h | (v & 1);
    x: long = i64ToF64(h);
    return f64Arith(0, x, x);
}
pub u64ToF32 v:long -> long {
    if (v >= 0) { return i64ToF32(v); }
    h: long = ((v as u64) >> (1 as u64)) as long;
    h = h | (v & 1);
    x: long = i64ToF32(h);
    return f32Arith(0, x, x);
}

// Toward zero to a signed 64-bit integer. NaN and anything outside the range give the most
// negative long, which is what `cvttsd2si` answers.
pub f64ToI64 v:long -> long {
    r: long = 0;
    unsafe { asm { in rax v; "movq xmm0, rax" "cvttsd2si rax, xmm0" out r rax; } }
    return r;
}
pub f32ToI64 v:long -> long {
    r: long = 0;
    unsafe { asm { in rax v; "movd xmm0, eax" "cvttss2si rax, xmm0" out r rax; } }
    return r;
}

// Toward zero to an unsigned 64-bit integer. A value at or above 2^63 has 2^63 taken off before
// the signed conversion and the top bit set after it. NaN gives 2^63, as any value out of range
// does.
pub F64_TWO63: long = 4890909195324358656;    // 2^63 as an f64: 0x43E0000000000000
pub F32_TWO63: long = 1593835520;             // 2^63 as an f32: 0x5F000000
pub f64ToU64 v:long -> long {
    if (!fpCompare(5, v, F64_TWO63, false)) { return f64ToI64(v); }
    return f64ToI64(f64Arith(1, v, F64_TWO63)) ^ F64_SIGN;
}
pub f32ToU64 v:long -> long {
    if (!fpCompare(5, v, F32_TWO63, true)) { return f32ToI64(v); }
    return f32ToI64(f32Arith(1, v, F32_TWO63)) ^ F64_SIGN;
}

pub f32ToF64 v:long -> long {
    r: long = 0;
    unsafe { asm { in rax v; "movd xmm0, eax" "cvtss2sd xmm0, xmm0" "movq rax, xmm0" out r rax; } }
    return r;
}
pub f64ToF32 v:long -> long {
    r: long = 0;
    unsafe { asm { in rax v; "movq xmm0, rax" "cvtsd2ss xmm0, xmm0" "movd eax, xmm0" out r rax; } }
    return canonF32(r);
}

// ─── decimal text to the nearest float ───────────────────────────────────────

// The literal's spelling (`1.5`, `2.0e10`, `1e-3`, `-0.25`), correctly rounded to the nearest
// f64, or (`single`) f32, ties to even; a magnitude past the largest finite one is infinity, one
// below the smallest subnormal's half is zero. The digits are a big integer D and the value
// D * 10^E; the quotient or product is taken exactly and only the last step rounds.
pub decimalToFloat text:str single:bool -> long {
    neg: bool = false;
    i: long = 0;
    if (i < text.len && charAt(text, i) == '-') { neg = true; i = i + 1; }
    d: Vec<long>;                 // the significant digits, as a big integer: 32-bit limbs, low first
    exp10: long = 0;
    seenDot: bool = false;
    any: bool = false;
    while (i < text.len) {
        c: long = charAt(text, i);
        if (c == '.') { seenDot = true; i = i + 1; continue; }
        if (c == '_') { i = i + 1; continue; }
        if (c < '0' || c > '9') { break; }
        if (any || c != '0') {
            bigMulAdd(&d, 10, c - '0');
            any = true;
        }
        if (seenDot) { exp10 = exp10 - 1; }
        i = i + 1;
    }
    if (i < text.len && (charAt(text, i) == 'e' || charAt(text, i) == 'E')) {
        i = i + 1;
        eneg: bool = false;
        if (i < text.len && (charAt(text, i) == '+' || charAt(text, i) == '-')) {
            eneg = charAt(text, i) == '-';
            i = i + 1;
        }
        e: long = 0;
        while (i < text.len && charAt(text, i) >= '0' && charAt(text, i) <= '9') {
            if (e < 100000) { e = e * 10 + (charAt(text, i) - '0'); }
            i = i + 1;
        }
        if (eneg) { exp10 = exp10 - e; } else { exp10 = exp10 + e; }
    }
    p: long = 53;
    minExp: long = 0 - 1022;
    maxExp: long = 1023;
    if (single) { p = 24; minExp = 0 - 126; maxExp = 127; }
    sign: long = 0;
    if (neg) { if (single) { sign = F32_SIGN; } else { sign = F64_SIGN; } }
    if (!any || bigIsZero(d)) { return sign; }
    // Far out of range either way: the big numbers below would only say so slowly.
    if (exp10 + bigDigits(d) > 400) { return sign | infBits(single); }
    if (exp10 + bigDigits(d) < 0 - 400) { return sign; }

    // value = num / den * 2^(-k), num and den big integers, with the quotient carrying at least
    // p + 2 bits so the rounding bits are real ones.
    num: Vec<long> = d;
    den: Vec<long>;
    den.push(1);
    if (exp10 >= 0) { for j in 0..exp10 { bigMulAdd(&num, 10, 0); } }
    else { for j in 0..(0 - exp10) { bigMulAdd(&den, 10, 0); } }
    k: long = p + 3 + bigBits(den) - bigBits(num);
    if (k < 0) { k = 0; }
    bigShl(&num, k);
    q: Vec<long>;
    rem: bool = bigDivide(num, den, &q);   // q = num / den, rem: was there a remainder
    L: long = bigBits(q);
    lead: long = L - 1 - k;                 // the binary exponent of the leading bit
    // Below the smallest normal exponent the significand has fewer bits to keep.
    keepBits: long = p;
    if (lead < minExp) { keepBits = p - (minExp - lead); }
    if (keepBits < 0) { return sign; }    // under half the smallest subnormal: zero
    drop: long = L - keepBits;
    m: long = 0;
    if (drop <= 0) { m = bigLow64(q) << (0 - drop); drop = 0; }
    else {
        m = bigShrLow64(q, drop);
        half: bool = bigBit(q, drop - 1);
        sticky: bool = rem || bigAnyBelow(q, drop - 1);
        if (half && (sticky || (m & 1) != 0)) { m = m + 1; }
    }
    // Rounding up may carry into a new bit: one more of exponent.
    if (keepBits == p && m == (1 << p)) { m = m >> 1; lead = lead + 1; }
    if (keepBits < p && m == (1 << keepBits)) { lead = lead + 1; }   // a subnormal rounded up into a normal
    fracBits: long = p - 1;
    if (lead > maxExp) { return sign | infBits(single); }
    out: long = 0;
    if (lead < minExp || (keepBits < p && m < (1 << (p - 1)))) {
        // Subnormal: no implicit bit, a zero exponent field.
        out = m;
    } else {
        bias: long = 1023;
        if (single) { bias = 127; }
        out = ((lead + bias) << fracBits) | (m & ((1 << fracBits) - 1));
    }
    if (single) { return canonF32(sign | out); }
    return sign | out;
}

local infBits single:bool -> long {
    if (single) { return 2139095040; }            // 0x7F800000
    return 9218868437227405312;                   // 0x7FF0000000000000
}

// ─── big integers: 32-bit limbs in a Vec<long>, least significant first ──────

local LIMB: long = 4294967296;      // 2^32
local LIMB_MASK: long = 4294967295;

// x = x * m + a, for small m and a.
local bigMulAdd inout x:Vec<long> m:long a:long -> void {
    carry: long = a;
    for i in 0..x.len() {
        v: long = x.get(i) * m + carry;
        x.set(i, v & LIMB_MASK);
        carry = ((v as u64) >> (32 as u64)) as long;
    }
    while (carry != 0) { x.push(carry & LIMB_MASK); carry = ((carry as u64) >> (32 as u64)) as long; }
}

local bigIsZero x:Vec<long> -> bool {
    for i in 0..x.len() { if (x.get(i) != 0) { return false; } }
    return true;
}

// Significant bits.
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
            x.set(i, v & LIMB_MASK);
            carry = ((v as u64) >> (32 as u64)) as long;
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

// Any bit set below bit `b` (exclusive).
local bigAnyBelow x:Vec<long> b:long -> bool {
    if (b <= 0) { return false; }
    w: long = b / 32;
    for i in 0..w { if (i < x.len() && x.get(i) != 0) { return true; } }
    if (w < x.len() && (x.get(w) & ((1 << (b % 32)) - 1)) != 0) { return true; }
    return false;
}

local bigLow64 x:Vec<long> -> long {
    v: long = 0;
    if (x.len() > 0) { v = x.get(0); }
    if (x.len() > 1) { v = v | (x.get(1) << 32); }
    return v;
}

// The bits from `s` upward, as many as fit: what is left of x shifted right by s.
local bigShrLow64 x:Vec<long> s:long -> long {
    v: long = 0;
    for b in 0..63 {
        if (bigBit(x, s + b)) { v = v | (1 << b); }
    }
    return v;
}

// q = n / d, by binary long division from the top bit down; answers whether a remainder is left.
local bigDivide n:Vec<long> d:Vec<long> inout q:Vec<long> -> bool {
    q.clear();
    for i in 0..n.len() { q.push(0); }
    r: Vec<long>;
    nb: long = bigBits(n);
    b: long = nb - 1;
    while (b >= 0) {
        bigShl(&r, 1);
        if (bigBit(n, b)) {
            if (r.len() == 0) { r.push(1); } else { r.set(0, r.get(0) | 1); }
        }
        if (bigCmp(r, d) >= 0) {
            bigSub(&r, d);
            q.set(b / 32, q.get(b / 32) | (1 << (b % 32)));
        }
        b = b - 1;
    }
    return !bigIsZero(r);
}

local bigCmp a:Vec<long> b:Vec<long> -> long {
    n: long = a.len();
    if (b.len() > n) { n = b.len(); }
    i: long = n - 1;
    while (i >= 0) {
        x: long = 0;
        y: long = 0;
        if (i < a.len()) { x = a.get(i); }
        if (i < b.len()) { y = b.get(i); }
        if (x != y) { if (x < y) { return -1; } return 1; }
        i = i - 1;
    }
    return 0;
}

// a = a - b, with a >= b.
local bigSub inout a:Vec<long> b:Vec<long> -> void {
    borrow: long = 0;
    for i in 0..a.len() {
        y: long = borrow;
        if (i < b.len()) { y = y + b.get(i); }
        v: long = a.get(i) - y;
        if (v < 0) { v = v + LIMB; borrow = 1; } else { borrow = 0; }
        a.set(i, v);
    }
}
