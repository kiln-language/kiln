// Deque<T>: a double-ended queue over a growable ring buffer. Push and pop at either end are
// O(1) amortized, so one type is a stack, a queue and a deque; the same thing over a Vec would
// make every dequeue an O(n) shift.
//
// `head` is the physical index of the logical front, and logical i sits at
// `(head + i) & (cap - 1)`. Capacity is always a power of two so that wrap is a mask. Growth
// doubles and re-linearizes, since a raw copy of a wrapped ring would scramble it. That takes two
// block copies (the run from `head` to the ring's end, then the wrapped remainder).
//
// Any element type, like Vec: push and pop move a value in and out, `q[i]` is a borrow of the
// element in place, and only `get`/`front`/`back`, which hand out a copy, need `Copy`. An
// owning element is released when it is popped and bound, when it is overwritten, and with the
// deque. Every index is bounds-checked.
//
// Not internally synchronized: to share one, wrap it in a `Mutex<Deque<T>>`.
//
//     q: Deque<int>;                  // Default: empty, no allocation
//     q.pushBack(1); q.pushBack(2);
//     q.pushFront(0);                 // [0, 1, 2]
//     first: int = q.popFront();      // 0
#include <{core, panic, heap, mem, option}>

// Each of these ends the program, naming the end or the index it was asked for.
local dequeEmpty what:str -> never { panicState(what, "deque is empty"); }

// cap is 0 (unallocated) or a power of two, so the wrap in `slot` can be a mask.
pub struct Deque<T> { ptr: *T, cap: long, head: long, count: long }

methods Deque<T> for Default {
    new -> Deque<T> { unsafe { return Deque { ptr: 0 as *T, cap: 0, head: 0, count: 0 }; } }
}

methods Deque<T> for Drop {
    drop &self -> void {
        self.clear();                                    // releases the elements, if T needs it
        unsafe { if (self.cap > 0) { free(self.ptr); } }
    }
}

methods Deque<T> {
    len     &self -> long { return self.count; }
    cap     &self -> long { return self.cap; }
    isEmpty &self -> bool { return self.count == 0; }

    // Physical slot of logical element i; callers bounds-check first.
    slot &self i:long -> long { return (self.head + i) & (self.cap - 1); }

    // Room for `need` elements, re-linearized so the front lands at index 0.
    reserve &self need:long -> void {
        if (need <= self.cap) { return; }
        ncap: long = 4;                                 // a power of two, so the mask stays valid
        while (ncap < need || ncap < self.cap * 2) { ncap = ncap * 2; }

        esz: long = sizeof(T);
        unsafe {
            nd: *T = malloc(ncap * esz) as *T;
            if (self.count > 0) {
                first: long = self.cap - self.head;     // from head to the ring's end
                if (first > self.count) { first = self.count; }
                memcpy(nd, self.ptr + self.head, first * esz);
                if (first < self.count) {               // the part that wrapped to index 0
                    memcpy(nd + first, self.ptr, (self.count - first) * esz);
                }
            }
            if (self.cap > 0) { free(self.ptr); }
            self.ptr = nd;
        }
        self.cap = ncap;
        self.head = 0;
    }

    pushBack &self v:T -> void {
        self.reserve(self.count + 1);
        unsafe { self.ptr[self.slot(self.count)] = v; }
        self.count += 1;
    }

    // Step head back one slot, wrapping, and write there. A Vec cannot do this cheaply.
    pushFront &self v:T -> void {
        self.reserve(self.count + 1);
        self.head = (self.head + self.cap - 1) & (self.cap - 1);
        self.count += 1;
        unsafe { self.ptr[self.slot(0)] = v; }
    }

    popFront &self -> T {
        if (self.count <= 0) { dequeEmpty("Deque.popFront"); }
        r: T;
        unsafe { r = self.ptr[self.slot(0)]; }
        self.head = (self.head + 1) & (self.cap - 1);
        self.count -= 1;
        return r;
    }

    popBack &self -> T {
        if (self.count <= 0) { dequeEmpty("Deque.popBack"); }
        r: T;
        unsafe { r = self.ptr[self.slot(self.count - 1)]; }
        self.count -= 1;
        return r;
    }

    // The same two, answering None on an empty deque instead of ending the program.
    tryPopFront &self -> Option<T> {
        if (self.count == 0) { return Option.None; }
        return Option.Some(self.popFront());
    }
    tryPopBack &self -> Option<T> {
        if (self.count == 0) { return Option.None; }
        return Option.Some(self.popBack());
    }

    // Replaces element i, releasing the one it replaces.
    set &self i:long v:T -> void {
        if (i < 0 || i >= self.count) { panicIndex("Deque.set", i, self.count); }
        unsafe {
            p: *T = self.ptr;
            k: long = self.slot(i);
            old: T = p[k];                               // moved out, so it is this scope's to drop
            p[k] = v;
        }
    }

    // Keeps the allocation; releases the elements when T needs it.
    clear &self -> void {
        unsafe {
            p: *T = self.ptr;
            for i in 0..self.count { gone: T = p[self.slot(i)]; }
        }
        self.count = 0;
        self.head = 0;
    }
}

// `q[i]`: a borrow of the element, for any element type.
methods Deque<T> for Index<long, T> {
    at &self i:long -> &T {
        if (i < 0 || i >= self.count) { panicIndex("Deque.at", i, self.count); }
        unsafe { return self.ptr[self.slot(i)]; }
    }
}
methods Deque<T> for IndexSet<long, T> {
    setAt &self i:long v:T -> void { self.set(i, v); }
}

// Reading without removing hands out a copy, which only a Copy element has to give.
// A deep copy (see Vec's Clone for why it has to be written out).
methods Deque<T: Clone> for Clone {
    clone &self -> Deque<T> {
        out: Deque<T>;
        for i in 0..self.count { out.pushBack(self.at(i).clone()); }
        return out;
    }
}

methods Deque<T: Copy> {
    front &self -> T {
        if (self.count <= 0) { dequeEmpty("Deque.front"); }
        return self.get(0);
    }
    back &self -> T {
        if (self.count <= 0) { dequeEmpty("Deque.back"); }
        return self.get(self.count - 1);
    }
    get &self i:long -> T {
        if (i < 0 || i >= self.count) { panicIndex("Deque.get", i, self.count); }
        unsafe { return self.ptr[self.slot(i)]; }
    }
}
