// Pool<T> — a generational arena: the value-semantics way to build graphs.
//
// Linked structures need many handles to the same node, which is exactly what safe references
// cannot express. A Pool sidesteps references: nodes live in one growable arena and are named
// by HANDLES — plain Copy {index, generation} values that can be stored in fields, passed
// around and duplicated freely. Safety is the generation check (the slotmap design):
//
//   - each slot carries a generation counter: even = vacant, odd = live;
//   - alloc bumps it even->odd and returns Handle { idx, that generation };
//   - free bumps it odd->even and threads the slot onto a free list;
//   - every access checks handle.gen == slot.gen, so a stale handle traps rather than reading
//     a slot that was freed or reused. That also rules out ABA: a reused slot has a later
//     generation than any old handle naming it.
//
// Slot layout: a `SlotHead` { gen, next } then the value, stride 16 + sizeof(T); `next` is the
// free-list link and is only meaningful while the slot is vacant. The arena is a `*u8` because
// the stride is not sizeof(T); the header is read through a `*SlotHead` and the payload through a
// `*T`, so touching a value is one machine access of exactly T's width.
//
//     nodes: Pool<int>;                    // Default: an empty pool
//     h: Handle = nodes.alloc(42);
//     nodes.free(h);
//     nodes.get(h);                        // TRAP: stale generation
#include <{core, panic, heap, mem}>

// A handle that names nothing live. Each cause is reported separately, because which one it
// is says what the bug is: out of range means the handle came from another pool or was built
// by hand, while a generation mismatch means it named a slot that has since been freed.
local poolStale what:str -> never { panicState("Pool.check", what); }

// A node name: plain data, safe to store anywhere. Comparable with `==` via the derived Eq.
pub struct Handle { idx: long, gen: long }

pub struct Pool<T> { data: *u8, cap: long, len: long, freeHead: long }

struct SlotHead { gen: long, next: long }
local SLOT_HEAD: long = 16;

methods Pool<T> for Default {
    // A small eager arena, so alloc's fast path never has to branch on a null one.
    new -> Pool<T> {
        n: long = 16;
        stride: long = 16 + sizeof(T);
        unsafe {
            p: *u8 = malloc(n * stride) as *u8;
            for i in 0..n { h: *SlotHead = (p + i * stride) as *SlotHead; h.gen = 0; }   // vacant
            return Pool { data: p, cap: n, len: 0, freeHead: 0 };
        }
    }
}
methods Pool<T> for Drop {
    drop &self -> void {
        unsafe {
            for i in 0..self.len {                              // release every live value
                if (self.headAt(i).gen % 2 == 1) { p: *T = self.valueAt(i); gone: T = *p; }
            }
            free(self.data);
        }
    }
}

// Any value type: a node is reached in place through `at(h)` (a borrow), moved in by `alloc`
// and out by `take`, and released by `free`, by `set` over it, and with the pool. `get`
// hands out a copy, so it alone asks for `Copy`, below.
methods Pool<T> {
    stride &self -> long { return 16 + sizeof(T); }
    // Callers validate the index first, through `check` or `grow`.
    unsafe slotAt &self idx:long -> *u8 { return self.data + idx * self.stride(); }
    unsafe headAt &self idx:long -> *SlotHead { return self.slotAt(idx) as *SlotHead; }
    unsafe valueAt &self idx:long -> *T { return (self.slotAt(idx) + SLOT_HEAD) as *T; }

    // Doubling growth. Slots keep their indices, so every outstanding handle stays valid —
    // which is the point of naming nodes by index.
    grow &self -> void {
        stride: long = self.stride();
        ncap: long = self.cap * 2;
        unsafe {
            nd: *u8 = malloc(ncap * stride) as *u8;
            memcpy(nd, self.data, self.cap * stride);
            for i in self.cap..ncap { h: *SlotHead = (nd + i * stride) as *SlotHead; h.gen = 0; }
            free(self.data);
            self.data = nd;
        }
        self.cap = ncap;
    }

    // Claim a slot — free list first, then fresh — store v, and name it.
    alloc &self v:T -> Handle {
        idx: long = 0;
        if (self.freeHead != 0) {
            idx = self.freeHead - 1;                            // head is idx+1; 0 means empty
            unsafe { self.freeHead = self.headAt(idx).next; }
        } else {
            if (self.len == self.cap) { self.grow(); }
            idx = self.len;
            self.len = self.len + 1;
        }
        g: long = 0;
        unsafe {
            head: *SlotHead = self.headAt(idx);
            g = head.gen + 1;                                   // even -> odd: live
            head.gen = g;
            val: *T = self.valueAt(idx);
            *val = v;
        }
        return Handle { idx: idx, gen: g };
    }

    // Validate a handle and hand back its payload pointer, so a caller reads or writes it with
    // one typed access. Traps on anything stale or malformed.
    unsafe check &self h:Handle -> *T {
        if (h.idx < 0 || h.idx >= self.len) { panicIndex("Pool.check: handle", h.idx, self.len); }
        if (h.gen % 2 == 0)    { poolStale("the handle was never live (a live generation is odd)"); }
        if (self.headAt(h.idx).gen != h.gen) { poolStale("the slot was freed, and may already hold something else"); }
        return self.valueAt(h.idx);
    }

    // Does `h` name a live node of this pool? The question `check` asks, answered instead of
    // trapped on: for a cache of handles that may have gone stale on purpose.
    isLive &self h:Handle -> bool {
        if (h.idx < 0 || h.idx >= self.len || h.gen % 2 == 0) { return false; }
        unsafe { return self.headAt(h.idx).gen == h.gen; }
    }

    // Mark the validated slot vacant and put it on the free list.
    unsafe vacate &self h:Handle -> void {
        head: *SlotHead = self.headAt(h.idx);
        head.gen = h.gen + 1;
        head.next = self.freeHead;
        self.freeHead = h.idx + 1;
    }

    // The node itself, in place. What a graph walk reads and writes.
    at &self h:Handle -> &T { unsafe { p: *T = self.check(h); return *p; } }
    // Replaces the node's value, releasing the old one.
    set &self h:Handle v:T -> void { unsafe { p: *T = self.check(h); old: T = *p; *p = v; } }

    // Bump the generation, invalidating every outstanding handle, release the value, and
    // thread the slot onto the free list.
    free &self h:Handle -> void {
        unsafe {
            p: *T = self.check(h);                              // validate before touching it
            gone: T = *p;                                       // moved out: released here
            self.vacate(h);
        }
    }
    // Free the slot and hand its value back instead of releasing it.
    take &self h:Handle -> T {
        unsafe {
            p: *T = self.check(h);
            out: T = *p;
            self.vacate(h);
            return out;
        }
    }

    // Allocated minus freed; walks the free list.
    size &self -> long {
        n: long = self.len;
        f: long = self.freeHead;
        while (f != 0) {
            n = n - 1;
            unsafe { f = self.headAt(f - 1).next; }
        }
        return n;
    }
}

// A copy of the node's value, which only a Copy value has to give.
methods Pool<T: Copy> {
    get &self h:Handle -> T { unsafe { p: *T = self.check(h); return *p; } }
}
