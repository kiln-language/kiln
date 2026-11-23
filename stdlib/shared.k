// Shared<T>: single-threaded shared mutable state, checked at runtime.
//
// Mutable value semantics statically forbids two handles to the same mutable value. Shared is
// the escape hatch: a refcounted heap cell, where clone makes another handle and Drop releases
// one, entered through `with`. An exclusivity flag traps on overlapping access instead of
// unwinding. It is Rust's RefCell, except a violation ends the program like a bounds failure.
//
//     s: Shared<long> = newShared(1);
//     t: Shared<long> = s.clone();       // second handle to the same cell
//     with s { s = s + 41; }             // exclusive for the block
//     with t { … }                       // fine: the first borrow ended at `}`
//
// The flag is a plain word, no atomics: this is the single-threaded answer, and thread-safe
// shared mutation is `Arc<Mutex<T>>` composition instead.
//
// Block layout: [ count:long | borrow:long | value:T ]: one allocation of mixed types, so the
// handle keeps a `*u8` and reads each part through a typed view. Touching the value is one
// machine access of exactly T's width.
#include <{core, panic, heap}>

// The aliasing bug the flag exists to catch, named at the point it is caught.
local sharedBusy what:str -> void {
    panicState(what, "already borrowed");
}

pub struct Shared<T> { ptr: *u8 }

pub newShared<T> v:T -> Shared<T> {
    unsafe {
        p: *u8 = malloc(16 + sizeof(T)) as *u8;
        head: *long = p as *long;
        head[0] = 1;                        // count
        head[1] = 0;                        // borrow flag: free
        val: *T = (p + 16) as *T;
        *val = v;
        return Shared { ptr: p };
    }
}

pub struct SharedGuard<T> { ptr: *u8 }

methods Shared<T> {
    unsafe head &self -> *long { return self.ptr as *long; }
    unsafe valuePtr &self -> *T { return (self.ptr + 16) as *T; }

    // Enter exclusive access for a `with s { … }` block. Traps if the cell is already held,
    // which is the aliasing bug the flag exists to catch. The guard counts as an owner of the
    // cell, so dropping every handle while the guard lives cannot free the cell under it.
    // `unsafe`: the guard keeps the cell held past this call, so the caller vouches that it ends
    // the borrow by dropping the guard. `with` does that, and is the safe way in.
    unsafe hold &self -> SharedGuard<T> {
        unsafe {
            h: *long = self.head();
            if (h[1] != 0) { sharedBusy("Shared.hold"); }
            h[1] = 1;
            h[0] = h[0] + 1;
        }
        return SharedGuard { ptr: self.ptr };
    }
    count &self -> long { unsafe { h: *long = self.head(); return h[0]; } }
    // Is a `with` block holding the cell right now? Code that might run inside one can check
    // this first instead of trapping.
    isHeld &self -> bool { unsafe { h: *long = self.head(); return h[1] != 0; } }
}
methods Shared<T: Copy> {
    // A one-shot copy out without holding; still refuses while a writer is active.
    read &self -> T {
        unsafe {
            h: *long = self.head();
            if (h[1] != 0) { sharedBusy("Shared.read"); }
            p: *T = self.valuePtr();
            return *p;
        }
    }
}
methods Shared<T> for Clone {
    clone &self -> Shared<T> {
        unsafe { h: *long = self.head(); h[0] = h[0] + 1; }
        return Shared { ptr: self.ptr };
    }
}
methods Shared<T> for Drop {
    drop &self -> void {
        unsafe {
            h: *long = self.head();
            h[0] -= 1;
            if (h[0] == 0) {
                p: *T = self.valuePtr();
                gone: T = *p;                                  // the last owner releases the value
                free(self.ptr);
            }
        }
    }
}

// Inside `with s { … }`, a read of `s` becomes at(), a borrow, so `s.field` reads and
// writes in place for any T. A write of `s` becomes set(), which releases what it
// overwrites.
methods SharedGuard<T> {
    at &self -> &T { unsafe { p: *T = (self.ptr + 16) as *T; return *p; } }
    set &self v:T -> void { unsafe { p: *T = (self.ptr + 16) as *T; old: T = *p; *p = v; } }
}
// A copy of the whole value, which only a Copy value has to give.
methods SharedGuard<T: Copy> {
    get &self -> T { unsafe { p: *T = (self.ptr + 16) as *T; return *p; } }
}
// At `}`: end the borrow, then give up the guard's share of the cell, releasing it if every
// handle has already gone.
methods SharedGuard<T> for Drop {
    drop &self -> void {
        unsafe {
            h: *long = self.ptr as *long;
            h[1] = 0;
            h[0] -= 1;
            if (h[0] == 0) {
                p: *T = (self.ptr + 16) as *T;
                gone: T = *p;
                free(self.ptr);
            }
        }
    }
}
