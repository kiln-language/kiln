// Iteration: one trait, and the iterators the stdlib provides for it.
//
//     it: Range = range(0, 5);
//     for x: long in it { println("{}", x); }
//
// `Iter<T>` takes a type parameter, so `Iter<long>` and `Iter<int>` are different contracts
// with different vtables — one trait serves every element type without erasing it.
//
// TAKE AN ITERATOR BY BOUND, NOT AS A TRAIT OBJECT:
//
//     sum<I: Iter<long>> inout it:I -> long      // direct calls; the inliner erases them
//     sum inout it:Iter<long> -> long            // two vtable calls PER ELEMENT, forever
//
// A bound monomorphizes, and the inliner folds the two methods into the loop. A trait object's
// indirect call has no known target and can never be inlined. Both compile; only one is free.
// `for x: T in it` inherits whichever you gave it.
//
// The protocol is `hasNext`/`next` rather than a `next` reporting exhaustion in its return.
// `next &self -> Option<T>` would compile as a trait method, and the trade is real: this shape
// costs nothing per element, that one builds and destructures a tagged union on every step
// including the last, in exchange for making a read past the end unrepresentable rather than a
// trap. Changing it would touch every adapter and the `for` desugar, which the compiler owns.
#include <{vec, core, panic, option}>

pub trait Iter<T> {
    hasNext &self -> bool;
    next    &self -> T;
}

// Reading past the end is a caller bug, and there is no value of an arbitrary T that means
// "nothing", so it ends the program — saying so, rather than as a bare SIGILL.
local trapIter -> void {
    panicState("Iter.next", "the iterator is exhausted — check hasNext first");
}

// ─── Range: the half-open integer range [lo, hi) ─────────────────────────────
pub struct Range { i: long, hi: long }

pub range lo:long hi:long -> Range { return Range { i: lo, hi: hi }; }

methods Range for Iter<long> {
    hasNext &self -> bool { return self.i < self.hi; }
    next &self -> long {
        if (self.i >= self.hi) { trapIter(); }
        v: long = self.i;
        self.i = self.i + 1;
        return v;
    }
}
methods Range for Default { new -> Range { return Range { i: 0, hi: 0 }; } }

// ─── StepRange: lo, lo+step, ... short of hi ─────────────────────────────────
// Either direction: a negative step counts down, and stops short of `hi` from above.
// `rangeStep(10, 0, -3)` yields 10, 7, 4, 1. A zero step yields nothing rather than forever.
pub struct StepRange { i: long, hi: long, step: long }

pub rangeStep lo:long hi:long step:long -> StepRange { return StepRange { i: lo, hi: hi, step: step }; }

methods StepRange for Iter<long> {
    hasNext &self -> bool {
        if (self.step > 0) { return self.i < self.hi; }
        if (self.step < 0) { return self.i > self.hi; }
        return false;
    }
    next &self -> long {
        if (!self.hasNext()) { trapIter(); }
        v: long = self.i;
        self.i = self.i + self.step;
        return v;
    }
}

// ─── VecIter: a Vec's elements, in order ─────────────────────────────────────
// Holds the buffer and length, not the Vec, so it is a BORROWED view with a slice's lifetime:
// growing the vector mid-walk leaves it on the old allocation. That is why `vecIter` is
// `unsafe` — the caller vouches for the vector outliving the walk. Everything after it is safe.
pub struct VecIter<T> { p: *T, n: long, i: long }

pub unsafe vecIter<T> inout v:Vec<T> -> VecIter<T> {
    return VecIter { p: v.buf.ptr, n: v.len(), i: 0 };
}

// Yields a BORROW of each element (`Iter<&T>`), never a copy, so it walks a Vec<String> as
// readily as a Vec<long> -- and for a scalar `&T` is the scalar, so `for x: long in it` is
// unchanged. An owning element is read in place: `for r: &Res in it { r.id }`.
methods VecIter<T> for Iter<&T> {
    hasNext &self -> bool { return self.i < self.n; }
    next &self -> &T {
        if (self.i >= self.n) { trapIter(); }
        k: long = self.i;
        self.i = k + 1;
        unsafe { return self.p[k]; }
    }
}

// ─── lazy adapters ───────────────────────────────────────────────────────────
// Each wraps another iterator and does its work in `next`, so nothing is computed until
// something asks and no intermediate sequence is built:
// `takeIter(mapIter(range(0, 1000000), &f), 3)` touches three elements, not a million.
//
// The parameters read `<T, I>` — element first, then the inner iterator — because a bound may
// only mention parameters already introduced, and `I: Iter<T>` needs `T` to its left. Each
// constructor learns `T` from `I`'s bound, so none has to be spelled out.
//
// `mapIter` and `filter` take a plain `fn`, not a closure: an adapter outlives the expression
// that builds it, and a closure may not leave the frame it was written in.

pub struct Take<T, I> { inner: I, left: long }

// At most `n` elements of `inner`.
pub takeIter<T, I: Iter<T>> inner:I n:long -> Take<T, I> { return Take { inner: inner, left: n }; }

methods Take<T, I: Iter<T>> for Iter<T> {
    // Asks the inner iterator only while the budget lasts, so a take over an endless iterator
    // still terminates.
    hasNext &self -> bool { return self.left > 0 && self.inner.hasNext(); }
    next &self -> T {
        if (self.left <= 0) { trapIter(); }
        self.left = self.left - 1;
        return self.inner.next();
    }
}

pub struct Skip<T, I> { inner: I, left: long }

// `inner` without its first `n` elements.
pub skipIter<T, I: Iter<T>> inner:I n:long -> Skip<T, I> { return Skip { inner: inner, left: n }; }

methods Skip<T, I: Iter<T>> for Iter<T> {
    // The skipping happens on the first question asked, not at construction — which is what
    // makes it lazy, and why `hasNext` is the one that drains.
    hasNext &self -> bool {
        while (self.left > 0 && self.inner.hasNext()) {
            self.inner.next();
            self.left = self.left - 1;
        }
        return self.inner.hasNext();
    }
    next &self -> T {
        if (!self.hasNext()) { trapIter(); }
        return self.inner.next();
    }
}

// U is what this yields; T is what the inner one yields.
pub struct Map<T, U, I> { inner: I, f: fn(T)->U }

pub mapIter<T, U, I: Iter<T>> inner:I f:fn(T)->U -> Map<T, U, I> {
    return Map { inner: inner, f: f };
}

methods Map<T, U, I: Iter<T>> for Iter<U> {
    hasNext &self -> bool { return self.inner.hasNext(); }
    next &self -> U { return self.f(self.inner.next()); }
}

// Holds one element of lookahead, because "is there another?" cannot be answered without
// finding it. The lookahead is an `Option<T>`: empty until `hasNext` finds one, taken by `next`,
// so the element is moved through rather than copied and any T will do.
pub struct Filter<T, I> { inner: I, pred: fn(T)->bool, slot: Option<T> }

pub filter<T, I: Iter<T>> inner:I pred:fn(T)->bool -> Filter<T, I> {
    return Filter { inner: inner, pred: pred, slot: Option.None };
}

methods Filter<T, I: Iter<T>> for Iter<T> {
    hasNext &self -> bool {
        if (self.slot.isSome()) { return true; }
        while (self.inner.hasNext()) {
            v: T = self.inner.next();
            if (self.pred(v)) { self.slot = Option.Some(v); return true; }
        }
        return false;
    }
    next &self -> T {
        if (!self.hasNext()) { trapIter(); }
        return self.slot.take().unwrap();
    }
}

// ─── consuming a chain ───────────────────────────────────────────────────────
// All take the iterator by bound, so their calls monomorphize like everything above.
//
// Named `count`, like `algo`'s. A name belongs to the module that declares it, so the two can
// coexist; a program including both modules writes `iter::count` or `algo::count`.
pub count<T, I: Iter<T>> inout it:I -> long {
    n: long = 0;
    while (it.hasNext()) { it.next(); n = n + 1; }
    return n;
}
pub sumLongs<I: Iter<long>> inout it:I -> long {
    t: long = 0;
    while (it.hasNext()) { t = t + it.next(); }
    return t;
}
// Everything left, in a Vec.
pub collect<T, I: Iter<T>> inout it:I -> Vec<T> {
    out: Vec<T>;
    while (it.hasNext()) { out.push(it.next()); }
    return out;
}
// The last element, or nothing if there were none.
pub lastOf<T, I: Iter<T>> inout it:I -> Option<T> {
    out: Option<T> = Option.None;
    while (it.hasNext()) { out = Option.Some(it.next()); }
    return out;
}
