// Ordering and hashing as contracts the type answers, so an algorithm takes them from its
// element type instead of from a comparator threaded through every call.
//
//     sort(&v);                    // ordered by the element's own Ord
//     sortBy(&v, ByDesc<long> { }); // or by a comparator, when the type's order is not the one
#include <core>

// Negative if self sorts before other, zero on a tie, positive after. Three-way rather than a
// `less` predicate: a comparison that already knows about equality does not have to be run a
// second time with the operands swapped to find it.
//
// `Self` names the implementing type, so an implementation cannot quietly order against
// something else. That also makes Ord a bound only: behind a vtable there is no receiver type
// left to name the second operand with.
pub trait Ord { cmp &self other:Self -> int; }

// Equal values must hash equally. Unequal values should hash differently, but a collision only
// slows the table down; it is not a bug in the type.
pub trait Hash { hash &self -> u64; }

// Named results for `cmp`: `orderOf(a.cmp(b)) == Ordering.Less`. `cmp` returns a plain `int` so
// an implementation can return a difference, and `orderOf` maps any such value to one of the
// three. `Ordering.Less as int` is -1, the value an implementation returns for "less".
pub enum Ordering: int { Less = -1, Equal, Greater }

pub orderOf c:long -> Ordering {
    if (c < 0) { return Ordering.Less; }
    if (c > 0) { return Ordering.Greater; }
    return Ordering.Equal;
}

// The smaller and the larger of two, by their own order; a tie answers the first. And `v` held
// to `lo..=hi`.
pub minOf<T: Ord> a:T b:T -> T { if (b.cmp(a) < 0) { return b; } return a; }
pub maxOf<T: Ord> a:T b:T -> T { if (b.cmp(a) > 0) { return b; } return a; }
pub clampTo<T: Ord> v:T lo:T hi:T -> T {
    if (v.cmp(lo) < 0) { return lo; }
    if (v.cmp(hi) > 0) { return hi; }
    return v;
}

// An ordering supplied from outside the type, for when the type's own is not the one you want:
// descending, by one field, by a key computed once up front.
//
// A struct rather than a bare `fn(T,T)->int` so a comparator can carry that key, and because
// a struct's `compare` monomorphizes to a direct call the inliner can erase, where a function
// pointer is an indirect call at every comparison and the inliner never touches one. That is
// worth about 15% on a large sort; see sort.k.
pub trait Compare<T> { compare &self a:T b:T -> int; }

// The element type's own order. No fields: the ordering is in the type, so there is nothing
// to carry and the comparator costs nothing to pass.
pub struct ByOrd<T> { }
methods ByOrd<T: Ord> for Compare<T> {
    compare &self a:T b:T -> int { return a.cmp(b); }
}

// The same order, reversed.
pub struct ByDesc<T> { }
methods ByDesc<T: Ord> for Compare<T> {
    compare &self a:T b:T -> int { return b.cmp(a); }
}

// A plain function, for an ordering with no type to hang off. This one costs an indirect call
// per comparison, which the other two avoid.
pub struct ByFn<T> { f: fn(T,T)->int }
methods ByFn<T> for Compare<T> {
    compare &self a:T b:T -> int { return self.f(a, b); }
}

// One mixer, so every scalar's hash is this function at a different width. Two rounds of
// multiply-and-xorshift: an open-addressed table masks the hash down to its low bits, so a
// key whose low bits barely move (a counter, a pointer, a small enum) must have its high
// bits folded down or every one of them probes the same handful of slots.
//
// The FNV prime and the same 29/32 shifts `hashBytes` finishes with, for one avalanche in the
// library rather than two that drift apart. Shifts are logical here because the type is
// unsigned; on a signed long they would copy the sign bit down and destroy the high half.
pub mixHash v:u64 -> u64 {
    h: u64 = v * 1099511628211;
    h ^= (h >> 29);
    h *= 1099511628211;
    return h ^ (h >> 32);
}

// Fold a second hash into a first, for a type hashing several fields: order matters, so
// (a, b) and (b, a) land apart.
pub combineHash seed:u64 h:u64 -> u64 { return mixHash(seed ^ (h + 0x9e3779b9 + (seed << 6) + (seed >> 2))); }

// ─── the scalars ────────────────────────────────────────────────────────────
// Every integer type at once (`Integer`: i8/char, i16, int, long, u8, u16, u32, u64): `<` knows
// whether its operands are signed, so one body serves them all. Floats have neither; see float.k.
methods<T: Integer> T for Ord {
    cmp &self other:T -> int {
        if (self < other) { return -1; }
        if (self > other) { return 1; }
        return 0;
    }
}
methods<T: Integer> T for Hash { hash &self -> u64 { return mixHash(self as u64); } }

// The smaller, the larger, and the value held to [lo, hi], as f64 has them (float.k).
methods<T: Integer> T {
    min &self other:T -> T { if (other < self) { return other; } return self; }
    max &self other:T -> T { if (other > self) { return other; } return self; }
    clamp &self lo:T hi:T -> T {
        if (self < lo) { return lo; }
        if (self > hi) { return hi; }
        return self;
    }
}

methods bool for Ord { cmp &self other:bool -> int { return (self as u8).cmp(other as u8); } }
methods bool for Hash { hash &self -> u64 { return mixHash(self as u64); } }
