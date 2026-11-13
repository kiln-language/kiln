// RingBuffer<T, N> — a double-ended queue of at most N elements, held inline: `Deque` without the
// heap, for when the bound is part of the design.
//
//     q: RingBuffer<long, 16>;             // a bounded work queue
//     if (!q.pushBack(job)) { ... }        // false when full: back-pressure, not growth
//     next: long = q.popFront();
//
//     recent: RingBuffer<long, 100>;       // the last 100 of a stream
//     recent.pushEvict(sample);            // full: the oldest makes room, and is handed back
//
// Logical element i sits at `(head + i) % N`, so either end is O(1) and nothing ever moves. N need
// not be a power of two. Elements must be `Copy`, for the reason `InlineVec` gives: an inline
// array of an owning type keeps every slot alive at once.
#include <{core, panic, option, vec}>

pub struct RingBuffer<T: Copy, N: long> { data: [T; N], head: long, count: long }

methods RingBuffer<T, N> for Default {
    new -> RingBuffer<T, N> { return RingBuffer { head: 0, count: 0 }; }   // data: zero-filled
}

local ringEmpty what:str -> never { panicState(what, "the ring is empty"); }

methods RingBuffer<T, N> {
    len      &self -> long { return self.count; }
    capacity &self -> long { return N; }
    isEmpty  &self -> bool { return self.count == 0; }
    isFull   &self -> bool { return self.count == N; }

    // Physical slot of logical element i; callers check i first.
    slot &self i:long -> long { return (self.head + i) % N; }

    // Add at either end, or false when full.
    pushBack &self v:T -> bool {
        if (self.count == N) { return false; }
        self.data[self.slot(self.count)] = v;
        self.count = self.count + 1;
        return true;
    }
    pushFront &self v:T -> bool {
        if (self.count == N) { return false; }
        self.head = (self.head + N - 1) % N;
        self.data[self.head] = v;
        self.count = self.count + 1;
        return true;
    }
    // Add at the back, and when full make room by dropping the oldest, which comes back: the
    // "last N" shape. Nothing comes back while there was room.
    pushEvict &self v:T -> Option<T> {
        if (N == 0) { return Option.Some(v); }
        if (self.count < N) { self.pushBack(v); return Option.None; }
        old: T = self.data[self.head];
        self.data[self.head] = v;
        self.head = (self.head + 1) % N;
        return Option.Some(old);
    }

    popFront &self -> T {
        if (self.count == 0) { ringEmpty("RingBuffer.popFront"); }
        v: T = self.data[self.head];
        self.head = (self.head + 1) % N;
        self.count = self.count - 1;
        return v;
    }
    popBack &self -> T {
        if (self.count == 0) { ringEmpty("RingBuffer.popBack"); }
        self.count = self.count - 1;
        return self.data[self.slot(self.count)];
    }
    tryPopFront &self -> Option<T> {
        if (self.count == 0) { return Option.None; }
        return Option.Some(self.popFront());
    }
    tryPopBack &self -> Option<T> {
        if (self.count == 0) { return Option.None; }
        return Option.Some(self.popBack());
    }

    // Logical element i: 0 is the front, the oldest.
    get &self i:long -> T {
        if (i < 0 || i >= self.count) { panicIndex("RingBuffer.get", i, self.count); }
        return self.data[self.slot(i)];
    }
    front &self -> T { if (self.count == 0) { ringEmpty("RingBuffer.front"); } return self.get(0); }
    back  &self -> T { if (self.count == 0) { ringEmpty("RingBuffer.back"); } return self.get(self.count - 1); }

    clear &self -> void { self.head = 0; self.count = 0; }

    // Front to back, on the heap.
    toVec &self -> Vec<T> {
        out: Vec<T>;
        out.reserve(self.count);
        for i in 0..self.count { out.push(self.data[self.slot(i)]); }
        return out;
    }
}

// `q[i]`: logical element i, borrowed in place; `q[i] = v` replaces it.
methods RingBuffer<T, N> for Index<long, T> {
    at &self i:long -> &T {
        if (i < 0 || i >= self.count) { panicIndex("RingBuffer.at", i, self.count); }
        return self.data[self.slot(i)];
    }
}
methods RingBuffer<T, N> for IndexSet<long, T> {
    setAt &self i:long v:T -> void {
        if (i < 0 || i >= self.count) { panicIndex("RingBuffer.setAt", i, self.count); }
        self.data[self.slot(i)] = v;
    }
}
