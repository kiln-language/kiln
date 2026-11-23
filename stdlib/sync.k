// Locks, and the two things they compose with: a guarded value (`Mutex<T>`) and a guarded sink
// (`LockWriter<W>`). Every lock is entered through `with`, which drops its guard (and so
// releases the lock) at the closing `}` on every exit path, including an early `return`.
#include <{atomic, thread, write, option}>

// ─── LockGuard ──────────────────────────────────────────────────────────────
// The guard `hold()` returns. It has no get/set, so `with lock { … }` is hold-only: the body
// uses the guarded thing as-is.
//
// A plain store is the correct release on x86-64: it cannot tear, and TSO keeps every write
// made under the lock ahead of it.
local unsafe releaseLock flag:*int -> void { *flag = 0; }
pub struct LockGuard { flag: *int }
methods LockGuard for Drop {
    drop &self -> void { unsafe { releaseLock(self.flag); } }
}

// ─── SpinLock ───────────────────────────────────────────────────────────────
// An atomic flag: 0 free, 1 held. Uncontended acquire is one CAS. Under contention it does not
// hammer the atomic, which bounces the cache line between cores, but spins on a plain read
// (test-and-test-and-set) with PAUSE between reads, and yields the CPU after a bounded spin so
// the holder can actually run.
pub struct SpinLock { flag: AtomicInt, }

methods SpinLock for Default {
    new -> SpinLock {
        return SpinLock { flag: AtomicInt.new(0) };
    }
}
methods SpinLock {
    // `unsafe`: the guard keeps a pointer to the lock, so the caller vouches that the lock
    // outlives it. `with` does that, and is the safe way in.
    unsafe hold &self -> LockGuard {
        self.acquire();
        unsafe { return LockGuard { flag: &self.flag as *int }; }   // the flag is at offset 0
    }
    acquire &self -> void {
        loop {
            if (self.flag.cas(0, 1) == 0) { return; }
            spins: int = 0;
            while (self.flag.load() != 0) {              // contended: spin on a cheap read
                cpuRelax();
                spins += 1;
                if (spins >= 128) {
                    yieldNow();
                    spins = 0;
                }
            }
            // looked free, so loop back and race for it with the CAS again
        }
    }
    // One attempt, no blocking: true if this call took the lock.
    tryAcquire &self -> bool {
        return self.flag.casOk(0, 1);
    }
    release &self -> void {
        self.flag.store(0);
    }
}

// ─── Mutex<T> ───────────────────────────────────────────────────────────────
// A spin lock paired with the data it protects. The flag stays a concrete AtomicInt so the
// atomic op is fixed-width; only the guarded data is generic.
pub struct Mutex<T> { sl: SpinLock, data: T, }

pub newMutex<T> v:T -> Mutex<T> {
    return Mutex { sl: SpinLock.new(), data: v };
}
// Conditional: a Default Mutex builds its value from T's own Default, so
// `Mutex<BufWriter<FileOut>>` is Default while `Mutex<int>` simply is not.
methods Mutex<T: Default> for Default {
    new -> Mutex<T> { return Mutex { sl: SpinLock.new(), data: T.new() }; }
}

methods Mutex<T> {
    lock &self -> void { self.sl.acquire(); }
    unlock &self -> void { self.sl.release(); }
    unsafe hold &self -> LockGuard { return self.sl.hold(); }      // `unsafe`, as SpinLock.hold
    // The lock if it is free right now, without waiting: a guard to keep, or nothing. `unsafe`
    // for the same reason as `hold`.
    unsafe tryHold &self -> Option<LockGuard> {
        if (!self.sl.tryAcquire()) { return Option.None; }
        unsafe { return Option.Some(LockGuard { flag: &self.sl.flag as *int }); }
    }
}
// Copying the value out is Copy-only, since a Drop value would double-release. Non-Copy contents
// are reached in place: `with m { … m.data … }`.
methods Mutex<T: Copy> {
    get &self -> T { return self.data; }
    set &self v:T -> void { self.data = v; }
}

// ─── ReentrantMutex<T> ──────────────────────────────────────────────────────
// A mutex the same thread may lock again without deadlocking. It covers SpinLock's one
// hazard: code that reaches back into a lock it already holds. An owner thread-id and a
// recursion count over a plain SpinLock:
//   first lock          take the SpinLock, record owner = my tid, count = 1
//   re-lock, same thread   owner is already me, so bump the count: no atomic, no spin
//   unlock              only the last release clears the owner and frees the SpinLock
//
// `owner` is an AtomicLong so the fast-path read is a clean aligned load; `count` is only
// touched under the lock and needs no atomic.
pub struct ReentrantMutex<T> { sl: SpinLock, owner: AtomicLong, count: long, data: T, }

// Given typed pointers to the three control words, so it works whatever offset T puts the data
// at. The owner is cleared before the lock, or a thread that grabs the freed lock could have
// its own owner clobbered.
local unsafe reentrantRelease flag:*int owner:*long count:*long -> void {
    *count = *count - 1;
    if (*count == 0) {
        *owner = 0;
        releaseLock(flag);
    }
}

pub struct ReentrantGuard { flag: *int, owner: *long, count: *long }
methods ReentrantGuard for Drop {
    drop &self -> void { unsafe { reentrantRelease(self.flag, self.owner, self.count); } }
}

pub newReentrantMutex<T> v:T -> ReentrantMutex<T> {
    return ReentrantMutex { sl: SpinLock.new(), owner: AtomicLong.new(0), count: 0, data: v };
}
methods ReentrantMutex<T: Default> for Default {
    new -> ReentrantMutex<T> {
        return ReentrantMutex { sl: SpinLock.new(), owner: AtomicLong.new(0), count: 0, data: T.new() };
    }
}
methods ReentrantMutex<T> {
    acquire &self -> void {
        me: long = threadId();
        if (self.owner.load() == me) {         // already ours: just recurse
            self.count += 1;
            return;
        }
        self.sl.acquire();                     // first entry: block, then claim it
        self.owner.store(me);
        self.count = 1;
    }
    release &self -> void { unsafe { reentrantRelease(&self.sl.flag as *int, &self.owner as *long, &self.count as *long); } }
    lock &self -> void { self.acquire(); }
    unlock &self -> void { self.release(); }
    unsafe hold &self -> ReentrantGuard {                         // `unsafe`, as SpinLock.hold
        self.acquire();
        unsafe { return ReentrantGuard { flag: &self.sl.flag as *int, owner: &self.owner as *long, count: &self.count as *long }; }
    }
}
methods ReentrantMutex<T: Copy> {
    get &self -> T { return self.data; }
    set &self v:T -> void { self.data = v; }
}

// ─── LockWriter<W> ──────────────────────────────────────────────────────────
// Serializes each `write` of an inner sink. It is the opt-in way to make one thread-safe, since
// io.k's default stdout is unlocked by design. Composes like any decorator:
// `LockWriter<BufWriter<FileOut>>`.
pub struct LockWriter<W> { sl: SpinLock, inner: W }
methods LockWriter<W: Write> for Write {
    write &self ptr:long len:long -> long {
        held: LockGuard;                             // released at the closing brace
        unsafe { held = self.sl.hold(); }            // the lock is ours and outlives `held`
        return self.inner.write(ptr, len);
    }
}
pub newLockWriter<W: Write> inner:W -> LockWriter<W> {
    return LockWriter { sl: SpinLock.new(), inner: inner };
}
