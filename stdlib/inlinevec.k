// InlineVec<T, N> — a vector of at most N elements, held inline: no heap, ever.
//
//     xs: InlineVec<long, 8>;              // Default: empty
//     xs.push(3); xs.push(1);
//     if (!xs.tryPush(9)) { ... }          // false once it holds 8
//     first: long = xs[0];
//
// For small, bounded lists — a handful of operands, the arguments of one call, the last few
// results — where a `Vec` would spend an allocation on a few words, and for code that runs where
// the allocator is not available. A local one lives on the stack; one inside a struct is part of
// the struct.
//
// Elements must be `Copy`. An inline `[T; N]` of an owning type keeps all N alive from the
// declaration and releases all N at the end, which a vector that is mostly empty cannot be; so
// owning elements belong in a `Vec`. The bound is on the struct, so the refusal names the type
// where it is written.
#include <{core, panic, option, vec}>

pub struct InlineVec<T: Copy, N: long> { data: [T; N], count: long }

methods InlineVec<T, N> for Default {
    new -> InlineVec<T, N> { return InlineVec { count: 0 }; }       // data: zero-filled
}

local inlineFull what:str -> never { panicState(what, "the vector is full — its capacity is its type's N"); }
local inlineEmpty what:str -> never { panicState(what, "the vector is empty"); }

methods InlineVec<T, N> for AsSlice<T> {
    asSlice &self -> [T] { return self.data[..self.count]; }
}

methods InlineVec<T, N> {
    len      &self -> long { return self.count; }
    capacity &self -> long { return N; }
    isEmpty  &self -> bool { return self.count == 0; }
    isFull   &self -> bool { return self.count == N; }

    // Append, or false when full. `push` is the form that treats full as a bug.
    tryPush &self v:T -> bool {
        if (self.count == N) { return false; }
        self.data[self.count] = v;
        self.count = self.count + 1;
        return true;
    }
    push &self v:T -> void { if (!self.tryPush(v)) { inlineFull("InlineVec.push"); } }

    pop &self -> T {
        if (self.count == 0) { inlineEmpty("InlineVec.pop"); }
        self.count = self.count - 1;
        return self.data[self.count];
    }
    tryPop &self -> Option<T> {
        if (self.count == 0) { return Option.None; }
        return Option.Some(self.pop());
    }

    get &self i:long -> T {
        if (i < 0 || i >= self.count) { panicIndex("InlineVec.get", i, self.count); }
        return self.data[i];
    }
    set &self i:long v:T -> void {
        if (i < 0 || i >= self.count) { panicIndex("InlineVec.set", i, self.count); }
        self.data[i] = v;
    }
    first &self -> T { if (self.count == 0) { inlineEmpty("InlineVec.first"); } return self.data[0]; }
    last  &self -> T { if (self.count == 0) { inlineEmpty("InlineVec.last"); } return self.data[self.count - 1]; }

    // At position i (0..len), shifting the tail right; false when full.
    insert &self i:long v:T -> bool {
        if (i < 0 || i > self.count) { panicIndex("InlineVec.insert", i, self.count); }
        if (self.count == N) { return false; }
        k: long = self.count;
        while (k > i) { self.data[k] = self.data[k - 1]; k = k - 1; }
        self.data[i] = v;
        self.count = self.count + 1;
        return true;
    }
    // Remove element i, shifting the tail left to keep the order.
    removeAt &self i:long -> T {
        if (i < 0 || i >= self.count) { panicIndex("InlineVec.removeAt", i, self.count); }
        r: T = self.data[i];
        for k in i..self.count - 1 { self.data[k] = self.data[k + 1]; }
        self.count = self.count - 1;
        return r;
    }
    // Remove element i by moving the last one into its place: O(1), order not kept.
    swapRemove &self i:long -> T {
        if (i < 0 || i >= self.count) { panicIndex("InlineVec.swapRemove", i, self.count); }
        r: T = self.data[i];
        self.count = self.count - 1;
        self.data[i] = self.data[self.count];
        return r;
    }

    clear    &self -> void { self.count = 0; }
    truncate &self n:long -> void { if (n >= 0 && n < self.count) { self.count = n; } }

    // As many of `xs` as fit; answers how many that was.
    extendSlice &self xs:[T] -> long {
        n: long = 0;
        while (n < xs.len && self.tryPush(xs[n])) { n = n + 1; }
        return n;
    }
    // The elements, on the heap, for when they must grow past N or outlive this.
    toVec &self -> Vec<T> {
        out: Vec<T>;
        out.reserve(self.count);
        for i in 0..self.count { out.push(self.data[i]); }
        return out;
    }
}

// `xs[i]` borrows the element in place; `xs[i] = v` replaces it. Both check against the length,
// not the capacity: a slot past `len` holds no element.
methods InlineVec<T, N> for Index<long, T> {
    at &self i:long -> &T {
        if (i < 0 || i >= self.count) { panicIndex("InlineVec.at", i, self.count); }
        return self.data[i];
    }
}
methods InlineVec<T, N> for IndexSet<long, T> {
    setAt &self i:long v:T -> void { self.set(i, v); }
}
