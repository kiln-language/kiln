// Block moves, and moving a value out of a place that must stay valid.
//
// The block copy is the one memory primitive worth a dedicated function — `rep movsb`/`rep
// stosb` are microcoded and widen internally, which a byte-at-a-time typed loop cannot match.
// A single load or store needs nothing from here: `*p` and `p[i]` on a typed pointer are the
// language's own, and say the width in the type.
//
// The compile-time evaluator cannot run `asm`, so there they are word loops, then bytes.
#include <core>

// Copy `n` bytes dst <- src. The ranges must not overlap. `unsafe`: the caller vouches for both
// ranges.
pub unsafe memcpy dst:long src:long n:long -> void {
    if (atCompileTime()) {
        i: long = 0;
        while (i + 8 <= n) { *((dst + i) as *long) = *((src + i) as *long); i = i + 8; }
        while (i < n) { *((dst + i) as *u8) = *((src + i) as *u8); i = i + 1; }
        return;
    }
    asm { in rdi dst; in rsi src; in rcx n; "rep movsb" }
}

// Fill `n` bytes at `dst` with the low byte of `v`.
pub unsafe memset dst:long v:long n:long -> void {
    if (atCompileTime()) {
        word: long = (v & 255) * 0x0101010101010101;
        i: long = 0;
        while (i + 8 <= n) { *((dst + i) as *long) = word; i = i + 8; }
        while (i < n) { *((dst + i) as *u8) = v as u8; i = i + 1; }
        return;
    }
    asm { in rdi dst; in rax v; in rcx n; "rep stosb" }   // stosb writes AL, the low byte of rax
}

// ─── take / replace ───────────────────────────────────────────────────────────
//
// "Move this out and leave something valid behind." Moving a Drop field out of a borrowed struct
// is refused, and rightly: the owner would release it too. What IS sound is a swap — the place
// gets a fresh value in the same breath, so it is definitely initialized again and every
// existing check holds.
//
//     out: Vec<long> = take(&self.items);      // items is now empty; out owns what it held
//     inner: Vec<long> = take(outer.at(0));    // own an element out of a Vec<Vec<T>>
//
// The second line is what makes a container of owning containers usable: `at` hands out a borrow
// and `get` needs `Copy`, so without this there is no way to OWN an inner value at all.
//
// The swap is a byte exchange of `T`, which is exactly what a move is; the value that was in `t`
// is now in the result and nothing has two owners at any point. No local `T` ever holds a copy
// of a value that lives on somewhere else: such a local would be released at its end, taking the
// value with it. So the exchange goes through raw bytes (`swapBytes`), and `replace` hands back
// its own parameter, which after the exchange holds the old value and is moved out by `return`.
pub take<T: Default> inout t:T -> T {
    fresh: T = T.new();
    return replace(t, fresh);        // `t` is already the lend; `&t` would be a raw address
}

// The same, with the caller choosing what is left behind — for a type with no `Default`, or when
// the replacement is meaningful.
pub replace<T> inout t:T with:T -> T {
    unsafe { swapBytes(&t as long, &with as long, sizeof(T)); }
    return with;                     // now the old value; returning it is the one owner moving
}

// Exchange two places, through raw bytes only, so neither value is ever owned twice.
pub swapValues<T> inout a:T inout b:T -> void {
    unsafe { swapBytes(&a as long, &b as long, sizeof(T)); }
}

// Exchange `n` bytes at `a` and `b` in place, through a small scratch block on the stack that
// holds no value of either: no allocation, and nothing for a drop to see. The ranges must not
// overlap. `unsafe`: the caller vouches for both ranges, and for the exchange leaving each
// place holding a valid value.
pub unsafe swapBytes a:long b:long n:long -> void {
    scratch: [u8; 64];
    done: long = 0;
    while (done < n) {
        k: long = n - done;
        if (k > 64) { k = 64; }
        memcpy(&scratch as long, a + done, k);
        memcpy(a + done, b + done, k);
        memcpy(b + done, &scratch as long, k);
        done = done + k;
    }
}
