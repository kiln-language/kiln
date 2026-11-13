// Shared<T> — single-threaded shared MUTABLE state, checked at runtime.
//
// The one thing mutable value semantics forbids statically is two handles to the same mutable
// value. This is the sanctioned escape: a refcounted heap cell (clone = another handle, Drop =
// release) entered through `with`, with an exclusivity flag that TRAPS on overlap rather than
// unwinding. RefCell, with a bounds-failure ending.
//
//     s: Shared<long> = newShared(1);
//     t: Shared<long> = s.clone();       // second handle to the SAME cell
//     with s { s = s + 41; }             // exclusive for the block
//     with t { … }                       // fine — the first borrow ended at `}`
//
// The flag is a plain word, no atomics: this is the single-threaded answer, and thread-safe
// shared mutation is `Arc<Mutex<T>>` composition instead.
//
// Block layout: [ count:long | borrow:long | value:T ] — one allocation of mixed types, so the
// handle keeps a `*u8` and reads each part through a typed view. Touching the value is one
// machine access of exactly T's width.
#include <{core, panic, heap}>

// The aliasing bug the flag exists to catch, named at the point it is caught.
local sharedBusy what:str -> void {
    panicState(what, "the cell is already held — a second access would alias the first");
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

    // Enter exclusive access for a `with s { … }` block. Traps if the cell is already held —
    // the aliasing bug the flag exists to catch.
    hold &self -> SharedGuard<T> {
        unsafe {
            h: *long = self.head();
            if (h[1] != 0) { sharedBusy("Shared.hold"); }
            h[1] = 1;
        }
        return SharedGuard { ptr: self.ptr };
    }
    count &self -> long { unsafe { h: *long = self.head(); return h[0]; } }
    // Is a `with` block holding the cell right now? What lets code that might run inside one
    // ask before it traps.
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
            h[0] = h[0] - 1;
            if (h[0] == 0) {
                p: *T = self.valuePtr();
                gone: T = *p;                                  // the last owner releases the value
                free(self.ptr);
            }
        }
    }
}

// Inside `with s { … }`, a read of `s` becomes at() -- a borrow, so `s.field` reads and
// writes in place, for any T -- and a write of `s` becomes set(), which releases what it
// overwrites.
methods SharedGuard<T> {
    at &self -> &T { unsafe { p: *T = (self.ptr + 16) as *T; return *p; } }
    set &self v:T -> void { unsafe { p: *T = (self.ptr + 16) as *T; old: T = *p; *p = v; } }
}
// A copy of the whole value, which only a Copy value has to give.
methods SharedGuard<T: Copy> {
    get &self -> T { unsafe { p: *T = (self.ptr + 16) as *T; return *p; } }
}
methods SharedGuard<T> for Drop {
    drop &self -> void {
        unsafe { h: *long = self.ptr as *long; h[1] = 0; }   // release the borrow at `}`
    }
}
