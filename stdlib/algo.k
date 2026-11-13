// Higher-order algorithms over `Vec<T>`, parameterised by what you pass in: a closure, or a
// named function -- either satisfies an `Fn` bound, and each instantiates its own copy, so
// the call is direct and inlinable.
//
//     xs: Vec<long>;
//     xs.push(1); xs.push(2); xs.push(3);
//     println("{}", count(xs, |n: &long| n % 2 != 0));     // 2
//     retain(&xs, &isOdd);                                 // xs is now [1, 3]
//
// The vector is lent read-only to everything that only looks at it, so the caller writes
// `xs`; the three that write it -- `map`, `retain`, `mapInto`'s destination -- take it
// `inout`, so the caller writes `&xs`. A closure reads and writes what it captures, which is
// what makes a callback that depends on something outside itself a one-liner: a threshold,
// a running total, a vector being filled all live where they are and the closure reaches them.
#include <{vec, core, option, mem}>

// ─── inspecting ──────────────────────────────────────────────────────────────

// Every element is handed to the callback as a BORROW -- `v[i]`, so `Fn(&T)` -- and these work
// for any element type, owning or not; `map` is the one that writes.
pub each<T, F: Fn(&T) -> void> v:Vec<T> f:F -> void {
    for x in v { f(x); }
}

pub count<T, F: Fn(&T) -> bool> v:Vec<T> pred:F -> long {
    n: long = 0;
    for x in v { if (pred(x)) { n = n + 1; } }
    return n;
}

// The index of the first element satisfying `pred`, or -1. An index rather than an Option
// because an index is often what you wanted — it is what `lowerBound` reports and what you
// splice with. Reach for `findFirst` when it is the VALUE you are after.
pub find<T, F: Fn(&T) -> bool> v:Vec<T> pred:F -> long {
    for i in 0..v.len() { if (pred(v[i])) { return i; } }
    return -1;
}

// The first element satisfying `pred`, or nothing — no sentinel to compare against and no
// second lookup by index. Hands out a COPY, which is why this one keeps `Copy`: for an owning
// element, `find` gives the index and the element stays where it is.
pub findFirst<T: Copy, F: Fn(&T) -> bool> v:Vec<T> pred:F -> Option<T> {
    for x in v { if (pred(x)) { return Option.Some(x); } }
    return Option.None;
}

// Vacuously false for an empty vector.
pub any<T, F: Fn(&T) -> bool> v:Vec<T> pred:F -> bool {
    return find(v, pred) >= 0;
}

// Vacuously TRUE for an empty vector, which is why this is not `!any`.
pub all<T, F: Fn(&T) -> bool> v:Vec<T> pred:F -> bool {
    for x in v { if (!pred(x)) { return false; } }
    return true;
}

// ─── transforming ────────────────────────────────────────────────────────────

// In place, same type in and out. A mapping that CHANGES the type has to write somewhere else,
// which is `mapInto`. `Copy`, because `f` is handed the element by value and its result stored
// back; for an owning element, `mapOwned` takes each out and puts the result back.
pub map<T: Copy, F: Fn(T) -> T> inout v:Vec<T> f:F -> void {
    for i in 0..v.len() { v.set(i, f(v.get(i))); }
}

// The same for an element that owns something: each is moved out (leaving T's default in its
// slot for the moment), handed to `f` to consume, and the result moved back in.
pub mapOwned<T: Default, F: Fn(sink T) -> T> inout v:Vec<T> f:F -> void {
    for i in 0..v.len() {
        old: T = take(v.at(i));
        v.set(i, f(old));
    }
}

// Append `f` of every element of `src` onto `dst`, with `U` pinned by the destination. `f`
// borrows the element and builds the result, so neither side needs `Copy`.
pub mapInto<T, U, F: Fn(&T) -> U> src:Vec<T> inout dst:Vec<U> f:F -> void {
    dst.reserve(src.len());
    for x in src { dst.push(f(x)); }
}

// Keep the elements satisfying `pred`, preserving order. Compacts in place in one pass — no
// allocation, each survivor swapped down at most once, and the rejects released by `pop`.
pub retain<T, F: Fn(&T) -> bool> inout v:Vec<T> pred:F -> void {
    kept: long = 0;
    for i in 0..v.len() {
        if (pred(v[i])) {
            if (kept != i) { v.swap(kept, i); }
            kept = kept + 1;
        }
    }
    v.truncate(kept);                                    // the rejects, released
}

// Left fold. `U` is pinned by `init`, so the accumulator may be a different type from the
// element — summing a Vec<int> into a long, say. The accumulator is handed to `f` as a
// `sink`: the step consumes what it was given and returns the next, which is the shape that
// lets an owning accumulator (a String being built up) be carried without a copy per step.
pub fold<T, U, F: Fn(sink U, &T) -> U> v:Vec<T> init:U f:F -> U {
    acc: U = init;
    for x in v { acc = f(acc, x); }
    return acc;
}

pub reverse<T> inout v:Vec<T> -> void {
    i: long = 0;
    j: long = v.len() - 1;
    while (i < j) {
        v.swap(i, j);
        i = i + 1;
        j = j - 1;
    }
}
