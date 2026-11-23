// `recover { ... } else { ... }` at run time, and `raise`.
//
// This is not an error mechanism. `Result` and `Option` are: a function that can fail says so in
// its signature and its caller decides. `recover` abandons a whole unit of work (checking one
// function, parsing one declaration) and moves on to the next. `raise` carries no value and a
// `recover` cannot pick which raises it catches, so it cannot be used to catch one kind of
// failure and carry on. Whatever describes the failure is reported before raising, or recorded
// by the unit itself. Nothing in the standard library raises or recovers.
//
// A `recover` statement keeps a record in its own frame and links it into a chain kept per
// thread, whose head is the word at `TLS_RECOVER` in the thread's TLS page (`heap.k`). `raise`
// resumes at the innermost record's handler: it unlinks that record, puts back the stack and
// frame pointers the record saved, and jumps to the handler, which puts back the callee-saved
// registers the record kept. A `raise` with no `recover` armed is a panic.
//
// Why both a `recover` and a `raise` have to sit in `unsafe` code: a `raise` abandons every frame
// between it and the handler without running what those frames would have run on the way out.
//   * What they owned leaks: no `drop` runs for it, and a `with` guard taken in one of them is
//     never released. So a `SpinLock` or `Mutex` held there stays locked, and the next attempt
//     to take it waits forever.
//   * Code caught mid-update stays mid-update. That includes the standard library whenever it
//     calls back into yours: a closure passed to `algo`, a `Hash`, `Eq` or `Ord` impl a
//     `HashMap` or `sort` is using, a `Drop` impl. A `raise` from a comparator leaves a vector
//     half sorted with an owning element in two slots, so dropping it releases that element
//     twice. Code the library calls back must never raise. Running drops on the way out would
//     fix the leaks, not this: the half-sorted vector would be dropped all the same, so this
//     rule stays even if drops on `raise` are ever added.
//   * Neither end can see the frames in between, so the rule is about ownership: a `raise` and
//     the `recover` that catches it belong to one subsystem that owns every frame between them,
//     holds no lock across them, and leaves nothing half built that outlives the unit.
//   * OS resources leak with the frames. A server that recovers per request leaks that request's
//     socket on every raise. Open such resources outside the body and release them in the handler.
// The frame of the `recover` itself is not abandoned: the locals its body declared are released
// before the handler runs, each as its flag says.
//
// `unsafe` on a `raise` marks where raises start, as on a `recover` it marks where they land. It
// does not put the raise in any signature: a safe function that calls `raise` inside `unsafe`
// (the compiler's `fail` is one) vouches for every caller it has, and to them it is an ordinary
// call. The rule above is what that vouching covers.
//
// A `panic` is not a `raise`: it ends the program whether a `recover` is armed or not.
#include <{heap, panic}>

// The record, as the compiler lays it out (`RECORD_*` in `codegen::ir`):
//   [0]       the record armed before this one, 0 for none
//   [8]       where to resume: the statement's handler
//   [16] rsp and [24] rbp as they were when it was armed
//   [32..56]  r12 to r15, and [64..80] the low halves of xmm12 to xmm14, put back on resuming
// The compiler fills [8, 88) and links the record through `recoverLink`; `raise` reads [0, 32).

// Makes `rec` the innermost armed record and returns the one it replaces. A `recover` statement
// calls it with its record's address as it begins, keeps the answer in the record's first word,
// and hands that back here when its body ends. The compiler finds it by `@recover`.
@recover pub unsafe recoverLink rec:long -> long {
    prev: long = 0;
    at: long = TLS_RECOVER;
    asm {
        in rdi rec;
        in rcx at;
        "mov rax, [fs:rcx]"
        "mov [fs:rcx], rdi"
        out prev rax;
    }
    return prev;
}

// Whether a `recover` is armed on this thread, so that a `raise` now would reach a handler.
pub recoverArmed -> bool {
    head: long = 0;
    at: long = TLS_RECOVER;
    unsafe { asm { in rcx at; "mov rax, [fs:rcx]" out head rax; } }
    return head != 0;
}

// Leaves for the handler of the innermost armed `recover`, abandoning every frame in between.
// The handler runs with that record unlinked, so a `raise` there goes to the next one out.
// `unsafe`: the caller vouches that it and the `recover` that catches this own every frame
// in between (see the top of this file).
pub unsafe raise -> never {
    rec: long = 0;
    at: long = TLS_RECOVER;
    unsafe { asm { in rcx at; "mov rax, [fs:rcx]" out rec rax; } }
    if (rec == 0) { panicState("raise", "no `recover` is armed on this thread"); }
    unsafe {
        asm -> never {
            in rdi rec;
            in rcx at;
            "mov rax, [rdi]"
            "mov [fs:rcx], rax"
            "mov rsp, [rdi + 16]"
            "mov rbp, [rdi + 24]"
            "jmp qword [rdi + 8]"
        }
    }
}
