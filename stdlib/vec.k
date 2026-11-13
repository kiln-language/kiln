// Vec<T> — a growable, heap-backed, bounds-checked sequence, split the way a systems Vec is:
// `RawVec<T>` owns the allocation, the capacity and all the growth arithmetic; `Vec<T>` layers
// the live-element count and the sequence API on top. The split keeps the unsafe pointer math
// in one small place.
//
// The buffer is a typed `*T`, so an element is `p[i]` — one size-scaled machine access. The
// block copy appears only where a whole block really moves, which is growth.
//
// Growth is amortized doubling, so N pushes cost O(N) copies in total.
//
// AN ELEMENT NEED NOT BE `Copy`. What a method does with an element decides what it needs:
//
//   methods Vec<T>          moving one in or out, or around — push, pop, insert, removeAt,
//                           swap, set, clear — and the length. Available for every T.
//   methods Vec<T: Copy>    READING one without removing it — get, last. For a Copy type the
//                           bytes ARE the value, so handing back a copy costs nothing and
//                           leaves the vector's own copy intact.
//   methods Vec<T: Clone>   the same read for a type that owns something — cloneAt, lastClone.
//                           An owning element cannot be handed out by copying it: two owners
//                           of one buffer is a double free, so the duplicate must be explicit.
//
// So `Vec<String>` is an ordinary vector you can push to, pop from and reorder; only reading
// an element in place asks you to say whether you want a clone.
//
// A Vec is a value, exclusively owned, and not internally synchronized. To share one, wrap it —
// `Mutex<Vec<T>>` — and reach it under `with`.
//
//     xs: Vec<int>;                   // Default: empty, no allocation
//     xs.push(10); xs.push(20); xs.push(30);
//     first: int = xs.get(0);         // 10, bounds-checked
//     top:   int = xs.pop();          // 30
//     xs.insert(1, 99);               // [10, 99, 20]
//
//     names: Vec<String>;             // owning elements
//     names.push(stringOf("alpha"));
//     n: String = names.cloneAt(0);   // a clone, because the vector keeps its own
//     out: String = names.pop();      // or take it out entirely
//
// And written as a literal, `vec![...]` -- the macro at the end of this file:
//
//     v: Vec<long> = vec![1, 2, 3];        // typed by where it is stored
//     e: Vec<P>    = vec![];               // empty, typed the same way
//     vec![long: 1, 2, 3]                  // the element type named outright, for anywhere else
#include <{core, panic, heap, mem, option}>

// The same trap a slice or Pool bounds failure compiles to (SIGILL).
// Every one of these ends the program. They name the operation and the index because the
// stack trace a SIGILL leaves has neither.
local vecEmpty what:str -> never { panicState(what, "the vector is empty"); }

// ─── RawVec<T>: the owning allocation ───────────────────────────────────────
// A typed heap pointer (null while unallocated) and how many T's it can hold. Frees the block
// on Drop; knows nothing about how many elements are live.
pub struct RawVec<T> { ptr: *T, cap: long }

methods RawVec<T> for Default {
    new -> RawVec<T> { unsafe { return RawVec { ptr: 0 as *T, cap: 0 }; } }
}
methods RawVec<T> for Drop {
    drop &self -> void { unsafe { if (self.cap > 0) { free(self.ptr); } } }
}
// No bound: this moves BLOCKS, never individual values. Relocating the buffer is one memcpy
// of the bytes an element happens to occupy, which is as true of an owning element as a Copy
// one — the element is not duplicated, it is somewhere else afterwards.
methods RawVec<T> {
    // Room for at least `need` elements: grow to max(need, 2*cap, 4), through realloc (in place
    // when the block has the room, its pages moved when it is large, else a copy).
    reserve &self need:long -> void {
        if (need <= self.cap) { return; }
        ncap: long = self.cap * 2;
        if (ncap < need) { ncap = need; }
        if (ncap < 4)    { ncap = 4; }
        esz: long = sizeof(T);
        unsafe {
            if (self.cap > 0) { self.ptr = realloc(self.ptr as long, self.cap * esz, ncap * esz) as *T; }
            else { self.ptr = malloc(ncap * esz) as *T; }
        }
        self.cap = ncap;
    }
}

// ─── Vec<T>: the sequence ───────────────────────────────────────────────────
// Vec's Drop releases the LIVE ELEMENTS; `buf` then frees the block on its own, since a
// hand-written drop runs before the fields' glue. Derived glue alone would do only the second
// half, which is right for a Copy element and a leak for an owning one — the elements are
// the vector's to release, and nothing else knows how many are live.
pub struct Vec<T> { buf: RawVec<T>, count: long }

methods Vec<T> for Drop {
    drop &self -> void { self.clear(); }   // drops [0, count) if T needs it; a no-op otherwise
}

methods Vec<T> for Default {
    new -> Vec<T> {
        r: RawVec<T>;                            // Default: no allocation
        return Vec { buf: r, count: 0 };
    }
}
// Everything that MOVES an element rather than reading one: available for every T.
// A Vec of the arguments, in order: what `vec![a, b, c]` expands to, and usable as it is.
pub vecOf<T: Copy> xs:...T -> Vec<T> {
    v: Vec<T>;
    v.extendSlice(xs);
    return v;
}
// An empty one, as an expression: `vec![]`. T comes from where the result is stored.
pub emptyVec<T> -> Vec<T> { v: Vec<T>; return v; }

// What `for x in v` walks.
methods Vec<T> for AsSlice<T> {
    asSlice &self -> [T] { unsafe { return self.buf.ptr[..self.count]; } }
}

methods Vec<T> {
    len     &self -> long { return self.count; }
    cap     &self -> long { return self.buf.cap; }
    isEmpty &self -> bool { return self.count == 0; }

    // Room for `additional` more elements beyond the current length. `xs: Vec<T>;
    // xs.reserve(n)` is the with-capacity idiom — construction is Default, capacity a method.
    reserve &self additional:long -> void { self.buf.reserve(self.count + additional); }

    // Amortized O(1).
    push &self v:T -> void {
        self.buf.reserve(self.count + 1);
        unsafe { self.buf.ptr[self.count] = v; }
        self.count = self.count + 1;
    }

    pop &self -> T {
        if (self.count <= 0) { vecEmpty("Vec.pop"); }
        self.count = self.count - 1;
        unsafe { return self.buf.ptr[self.count]; }
    }
    // The last element, or None when there is none: `pop` for a caller that expects emptiness.
    tryPop &self -> Option<T> {
        if (self.count == 0) { return Option.None; }
        return Option.Some(self.pop());
    }

    // Replaces element i. The one it replaces is released first — overwriting an owning
    // element without dropping it leaks whatever it held.
    set &self i:long v:T -> void {
        if (i < 0 || i >= self.count) { panicIndex("Vec.set", i, self.count); }
        unsafe {
            p: *T = self.buf.ptr;
            old: T = p[i];       // moved out, so it is this scope's to drop
            p[i] = v;
        }
    }

    // The primitive every in-place reordering is built from.
    swap &self i:long j:long -> void {
        if (i < 0 || i >= self.count) { panicIndex("Vec.swap", i, self.count); }
        if (j < 0 || j >= self.count) { panicIndex("Vec.swap", j, self.count); }
        unsafe {
            p: *T = self.buf.ptr;
            t: T = p[i];
            p[i] = p[j];
            p[j] = t;
        }
    }

    // Insert at index i (0..len), shifting the tail right. O(n).
    insert &self i:long v:T -> void {
        if (i < 0 || i > self.count) { panicIndex("Vec.insert", i, self.count); }   // count is a valid position: append
        self.buf.reserve(self.count + 1);
        unsafe {
            p: *T = self.buf.ptr;
            k: long = self.count;
            while (k > i) { p[k] = p[k - 1]; k = k - 1; }    // [i, count) -> [i+1, count+1)
            p[i] = v;
        }
        self.count = self.count + 1;
    }

    // Remove element i (0..len-1), shifting the tail left. O(n).
    removeAt &self i:long -> T {
        if (i < 0 || i >= self.count) { panicIndex("Vec.removeAt", i, self.count); }
        r: T;
        unsafe {
            p: *T = self.buf.ptr;
            r = p[i];
            for k in i..self.count - 1 { p[k] = p[k + 1]; }   // (i, count) -> [i, count-1)
        }
        self.count = self.count - 1;
        return r;
    }

    // Keep the first `n` elements, releasing the rest (from the back) and keeping the capacity.
    // Each released element is moved out and dropped at the end of its turn; for a Copy element
    // that is nothing, so this stays a single store there.
    truncate &self n:long -> void {
        if (n < 0 || n >= self.count) { return; }
        unsafe {
            p: *T = self.buf.ptr;
            for i in n..self.count { gone: T = p[i]; }
        }
        self.count = n;
    }
    clear &self -> void { self.truncate(0); }
}

// `xs[i]` is a BORROW of the element -- read a field of it, call a method on it, write a field
// through it, hand it to a function that borrows -- and so it works for every element type: an
// owning element is never copied out, only reached. Binding it to a local copies, which a Copy
// type allows and an owning one refuses (clone it, or `pop`). `xs[i] = v` replaces the whole
// element, releasing the old one.
methods Vec<T> for Index<long, T> {
    at &self i:long -> &T {
        if (i < 0 || i >= self.count) { panicIndex("Vec.at", i, self.count); }
        unsafe { return self.buf.ptr[i]; }
    }
}
methods Vec<T> for IndexSet<long, T> {
    setAt &self i:long v:T -> void { self.set(i, v); }
}

// Reading an element WITHOUT removing it. For a Copy type the bytes are the value, so the
// vector keeps its own and the caller gets one for free.
methods Vec<T: Copy> {
    // Every element of `other`, appended. One `reserve` for the whole run rather than a growth
    // check per element, which is the point of having this rather than a push loop written out
    // at each call site. `other` is lent and keeps its elements, which is why this is here
    // rather than above: for an owning element, move them out one at a time with `pop`.
    extend &self other:Vec<T> -> void {
        self.reserve(other.len());
        for x in other { self.push(x); }
    }
    // The same from a slice: an array's elements, or a variadic's.
    extendSlice &self xs:[T] -> void {
        self.reserve(xs.len);
        for x in xs { self.push(x); }
    }
    // The first element; traps on an empty vector, like `last`.
    first &self -> T {
        if (self.count <= 0) { vecEmpty("Vec.first"); }
        return self.get(0);
    }

    get &self i:long -> T {
        if (i < 0 || i >= self.count) { panicIndex("Vec.get", i, self.count); }
        unsafe { return self.buf.ptr[i]; }
    }

    last &self -> T {
        if (self.count <= 0) { vecEmpty("Vec.last"); }
        return self.get(self.count - 1);
    }
}

// The same read for an element that OWNS something. There is no free copy to hand out — two
// owners of one buffer is a double free — so the duplicate is explicit, and named so at the
// call site. `pop` is still there when you want the element itself rather than a copy.
// A deep copy, each element cloned. Without it Clone would be derived field by field, and the
// copy would share this vector's buffer — and free it a second time.
methods Vec<T: Clone> for Clone {
    clone &self -> Vec<T> {
        out: Vec<T>;
        out.reserve(self.count);
        for i in 0..self.count { out.push(self.cloneAt(i)); }
        return out;
    }
}

methods Vec<T: Clone> {
    cloneAt &self i:long -> T {
        if (i < 0 || i >= self.count) { panicIndex("Vec.cloneAt", i, self.count); }
        unsafe { p: *T = self.buf.ptr; return p[i].clone(); }
    }

    lastClone &self -> T {
        if (self.count <= 0) { vecEmpty("Vec.lastClone"); }
        return self.cloneAt(self.count - 1);
    }
}

// `vec![ ... ]`: the compiler hands the macro the source between the brackets, it splits that
// on the commas between elements and reads each back as code where the macro was called, and
// the call becomes `vecOf(...)` -- or `emptyVec()` for nothing at all.
//
// A macro is written against `ast`'s `Node`, and `ast` holds a tree's children in a `Vec`, so
// this file cannot include `ast`. It need not: a macro declaration is read once the whole
// program has been, `ast` is in every program that declares one, and its names are visible
// from anywhere.
pub macro vec src:str -> Node {
    t: RawText = takePrefix(src, 1);
    tname: str = "";
    if (t.names.len() > 0) { tname = t.names.get(0); }
    pieces: Vec<str> = splitTopLevel(t.rest, "vec!");
    if (pieces.len() == 0) { return Node.Call("emptyVec", parseEach(pieces, "")); }
    return Node.Call("vecOf", parseEach(pieces, tname));
}
