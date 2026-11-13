// Atomics — the one place lock-prefixed asm lives, in two layers over the same instructions:
//
//   * `Atomic<T>` — a value you own. The value sits at offset 0, so `&self` IS its address, and
//     the `{rax}`/`{rcx}` placeholders render the operand at T's width, so one generic body is
//     correct for char, int and long alike.
//   * `atomicAdd`/`Sub`/`Cas`/`Swap`/`Load`/`Store` — the same operations against a `*long` you
//     already have (a heap word, a control block). `unsafe`, since the caller supplies the
//     address. heap.k's central pool and Arc's refcount run on these. They are the methods
//     below, called through the address: an `Atomic<long>` is exactly one long, so a `*long`
//     viewed as a `*Atomic<long>` is the same word, and the instructions exist once.
//
// x86-64 is TSO and a `lock`-prefixed instruction is a full barrier, so everything here is
// sequentially consistent. Plain aligned loads and stores of at most 8 bytes cannot tear and
// already carry acquire/release ordering, which is why `load`/`store` need no prefix.

// ─── Atomic<T>: an owned atomic value ───────────────────────────────────────

pub struct Atomic<T> { value: T }

methods Atomic<T> {
    new v:T -> Atomic<T> { return Atomic { value: v }; }

    load &self -> T { return self.value; }
    store &self v:T -> void { self.value = v; }

    // Fetch-and-add: returns the previous value.
    add &self delta:T -> T {
        old: T;
        unsafe { asm {
            in rax delta;
            in rbx self;
            "lock xadd [rbx], {rax}"
            out old rax;
        } }
        return old;
    }
    sub &self delta:T -> T { return self.add(-delta); }

    // Exchange. (`xchg` with a memory operand is implicitly locked.)
    swap &self v:T -> T {
        old: T;
        unsafe { asm {
            in rax v;
            in rbx self;
            "xchg [rbx], {rax}"
            out old rax;
        } }
        return old;
    }

    // Compare-and-swap. Returns the value that was there; == expected means it succeeded.
    cas &self expected:T desired:T -> T {
        old: T;
        unsafe { asm {
            in rax expected;
            in rcx desired;
            in rbx self;
            "lock cmpxchg [rbx], {rcx}"
            out old rax;
        } }
        return old;
    }
    // The same swap, answering the question you usually mean: did it take?
    casOk &self expected:T desired:T -> bool { return self.cas(expected, desired) == expected; }

    // x86's `lock and`/`or`/`xor` do not report what was there, so these are the standard CAS
    // retry loop: read, compute, swap it in if nothing changed underneath. Each returns the
    // previous value.
    fetchAnd &self mask:T -> T {
        loop {
            old: T = self.load();
            if (self.casOk(old, old & mask)) { return old; }
        }
    }
    fetchOr &self bits:T -> T {
        loop {
            old: T = self.load();
            if (self.casOk(old, old | bits)) { return old; }
        }
    }
    fetchXor &self bits:T -> T {
        loop {
            old: T = self.load();
            if (self.casOk(old, old ^ bits)) { return old; }
        }
    }
    // Raise the value to at least `v` / lower it to at most `v`; returns the previous value.
    // A high-water mark across threads is the usual reason to want one.
    fetchMax &self v:T -> T {
        loop {
            old: T = self.load();
            if (old >= v || self.casOk(old, v)) { return old; }
        }
    }
    fetchMin &self v:T -> T {
        loop {
            old: T = self.load();
            if (old <= v || self.casOk(old, v)) { return old; }
        }
    }
}

pub type AtomicInt = Atomic<int>;
pub type AtomicLong = Atomic<long>;

// ─── raw-address atomics ────────────────────────────────────────────────────

local unsafe atomicCell p:*long -> *Atomic<long> { return p as *Atomic<long>; }

pub unsafe atomicAdd   p:*long delta:long -> long { return atomicCell(p).add(delta); }
pub unsafe atomicSub   p:*long delta:long -> long { return atomicCell(p).sub(delta); }
pub unsafe atomicSwap  p:*long v:long -> long { return atomicCell(p).swap(v); }
pub unsafe atomicCas   p:*long expected:long desired:long -> long { return atomicCell(p).cas(expected, desired); }
// Named so a read of a word another thread writes says so, rather than looking like a plain
// access. No prefix needed — see the ordering note above.
pub unsafe atomicLoad  p:*long -> long { return *p; }
pub unsafe atomicStore p:*long v:long -> void { *p = v; }
