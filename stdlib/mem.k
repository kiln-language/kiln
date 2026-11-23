// Block moves, and moving a value out of a place that must stay valid.
//
// Block copy and fill get dedicated functions because `rep movsb`/`rep stosb` are microcoded
// and move wide chunks internally, which a byte-at-a-time typed loop cannot match. The copy is a
// compiler builtin, so the optimizer knows it writes the destination range and nothing else; the
// fill is `asm`. A single load or store needs nothing from here: `*p` and `p[i]` on a typed
// pointer are the language's own, and say the width in the type.
//
// The compile-time evaluator cannot run `asm`, so there `memset` is a word loop, then bytes.
#include <core>

// Copy `n` bytes dst <- src. The ranges must not overlap. `unsafe`: the caller vouches for
// both ranges. The compiler provides it: one `rep movsb` at run time, a byte loop in the
// compile-time evaluator.
pub unsafe builtin memcpy dst:long src:long n:long -> void;

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
// Move a value out and leave something valid behind. Moving a Drop field out of a borrowed
// struct is refused, since the owner would release it too. A swap is sound: the place gets a
// fresh value in the same step, so it stays initialized and every existing check holds.
//
//     out: Vec<long> = take(&self.items);      // items is now empty; out owns what it held
//     inner: Vec<long> = take(outer.at(0));    // own an element out of a Vec<Vec<T>>
//
// The second line matters for containers of owning containers: `at` hands out a borrow and `get`
// needs `Copy`, so `take` is the only way to get ownership of an inner value.
//
// The swap is a byte exchange of `T`, which is all a move is. The value that was in `t` ends up
// in the result, and nothing has two owners at any point. No local `T` may hold a copy of a
// value that also lives elsewhere, because the local would release it at scope end. So the
// exchange goes through raw bytes (`swapBytes`), and `replace` returns its own parameter, which
// holds the old value after the exchange.
pub take<T: Default> inout t:T -> T {
    fresh: T = T.new();
    return replace(t, fresh);        // `t` is already the lend; `&t` would be a raw address
}

// The same, with the caller choosing what is left behind, for a type with no `Default`, or when
// the replacement is meaningful.
pub replace<T> inout t:T with:T -> T {
    unsafe { swapBytes(&t as long, &with as long, sizeof(T)); }
    return with;                     // now the old value; returning it is the one owner moving
}

// Exchange two places, through raw bytes only, so neither value is ever owned twice.
pub swapValues<T> inout a:T inout b:T -> void {
    unsafe { swapBytes(&a as long, &b as long, sizeof(T)); }
}

// Exchange `n` bytes at `a` and `b` in place, a word at a time through a register and then the
// odd bytes: no allocation, no scratch, and nothing that holds a value of either, so nothing
// for a drop to see. Values swapped this way are small (a `take` or `replace` of one field),
// where three block copies through scratch spent most of their time starting up. The ranges
// must not overlap. `unsafe`: the caller vouches for both ranges, and for the exchange leaving
// each place holding a valid value.
pub unsafe swapBytes a:long b:long n:long -> void {
    i: long = 0;
    while (i + 8 <= n) {
        x: long = *((a + i) as *long);
        *((a + i) as *long) = *((b + i) as *long);
        *((b + i) as *long) = x;
        i += 8;
    }
    while (i < n) {
        y: u8 = *((a + i) as *u8);
        *((a + i) as *u8) = *((b + i) as *u8);
        *((b + i) as *u8) = y;
        i += 1;
    }
}
