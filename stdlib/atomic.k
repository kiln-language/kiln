// Atomics, in two layers over the same operations:
//
//   * `atomicLoad`, `atomicStore`, `atomicSwap`, `atomicCas`, `atomicAdd` and the rest: an
//     operation on a word you already have the address of (a heap word, a control block, a
//     word the kernel writes). They are compiler builtins, each one inlined instruction, and
//     the `32` forms take an `*int`. `unsafe`, since the caller supplies the address. heap.k's
//     central pool and Arc's refcount run on these.
//   * `Atomic<T>`: a value you own. The value sits at offset 0, so its address is the address
//     of `value`. A `long`-sized or `int`-sized T goes to the builtins above; a 1- or 2-byte T
//     falls back to one `asm` instruction, whose `{rax}`/`{rcx}` placeholders render the
//     operand at T's width.
//
// x86-64 is TSO. `add`, `swap` and `cas` are full barriers, so they are sequentially consistent.
// `load` is an acquire and `store` a release, which is all a lock, a flag or a published pointer
// needs. They are not a full barrier: a `store` followed by a `load` of a different word can be
// reordered, so code that needs that order (the Dekker pattern) stores with `atomicStoreSeqCst`
// or `swap`. The optimizer never removes, merges or moves an atomic, so a loop waiting for
// another thread to change a word reads memory every time round. Any other read of a word
// another thread writes at the same time is a data race, which the optimizer assumes never
// happens: it may keep such a read in a register for the whole loop.

// ─── on an address ──────────────────────────────────────────────────────────

pub unsafe builtin atomicLoad        p:*long -> long;                            // acquire
pub unsafe builtin atomicStore       p:*long v:long -> void;                     // release
pub unsafe builtin atomicStoreSeqCst p:*long v:long -> void;                     // full barrier
pub unsafe builtin atomicSwap        p:*long v:long -> long;                     // returns the old value
pub unsafe builtin atomicCas         p:*long expected:long desired:long -> long; // took iff old == expected
pub unsafe builtin atomicAdd         p:*long delta:long -> long;                 // returns the old value

pub unsafe builtin atomicLoad32        p:*int -> int;
pub unsafe builtin atomicStore32       p:*int v:int -> void;
pub unsafe builtin atomicStoreSeqCst32 p:*int v:int -> void;
pub unsafe builtin atomicSwap32        p:*int v:int -> int;
pub unsafe builtin atomicCas32         p:*int expected:int desired:int -> int;
pub unsafe builtin atomicAdd32         p:*int delta:int -> int;

pub unsafe atomicSub p:*long delta:long -> long { return atomicAdd(p, -delta); }

// ─── Atomic<T>: an owned atomic value ───────────────────────────────────────

pub struct Atomic<T> { value: T }

// `sizeof(T)` is a constant in each instance, so every method below compiles to one branch.
methods Atomic<T> {
    new v:T -> Atomic<T> { return Atomic { value: v }; }

    load &self -> T {
        unsafe {
            if (sizeof(T) == 8) { return atomicLoad(&self.value as *long) as T; }
            if (sizeof(T) == 4) { return atomicLoad32(&self.value as *int) as T; }
            v: T;
            asm {
                in rax self.value;        // only so `{rax}` takes T's width; the mov replaces it
                in rbx self;
                "mov {rax}, [rbx]"
                out v rax;
            }
            return v;
        }
    }
    store &self v:T -> void {
        unsafe {
            if (sizeof(T) == 8) { atomicStore(&self.value as *long, v as long); return; }
            if (sizeof(T) == 4) { atomicStore32(&self.value as *int, v as int); return; }
            asm {
                in rax v;
                in rbx self;
                "mov [rbx], {rax}"
            }
        }
    }

    // Fetch-and-add: returns the previous value.
    add &self delta:T -> T {
        unsafe {
            if (sizeof(T) == 8) { return atomicAdd(&self.value as *long, delta as long) as T; }
            if (sizeof(T) == 4) { return atomicAdd32(&self.value as *int, delta as int) as T; }
            old: T;
            asm {
                in rax delta;
                in rbx self;
                "lock xadd [rbx], {rax}"
                out old rax;
            }
            return old;
        }
    }
    sub &self delta:T -> T { return self.add(-delta); }

    // Exchange: returns the previous value.
    swap &self v:T -> T {
        unsafe {
            if (sizeof(T) == 8) { return atomicSwap(&self.value as *long, v as long) as T; }
            if (sizeof(T) == 4) { return atomicSwap32(&self.value as *int, v as int) as T; }
            old: T;
            asm {
                in rax v;
                in rbx self;
                "xchg [rbx], {rax}"           // implicitly locked with a memory operand
                out old rax;
            }
            return old;
        }
    }

    // Compare-and-swap. Returns the value that was there; == expected means it succeeded.
    cas &self expected:T desired:T -> T {
        unsafe {
            if (sizeof(T) == 8) {
                return atomicCas(&self.value as *long, expected as long, desired as long) as T;
            }
            if (sizeof(T) == 4) {
                return atomicCas32(&self.value as *int, expected as int, desired as int) as T;
            }
            old: T;
            asm {
                in rax expected;
                in rcx desired;
                in rbx self;
                "lock cmpxchg [rbx], {rcx}"
                out old rax;
            }
            return old;
        }
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
