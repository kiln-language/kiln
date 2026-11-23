// Threads over raw Linux syscalls (clone, futex, nanosleep, sched_yield): a child task sharing
// this process's address space.
//
// The clone trampoline stays file-private; only the complete operations are `pub`.
#include <{sys, core, panic, atomic}>

// ─── scheduling ─────────────────────────────────────────────────────────────

pub yieldNow -> void { unsafe { syscall0(Syscall.SchedYield); } }

// PAUSE: tells the core we are busy-waiting, so it saves power, frees the pipeline for a
// sibling hyperthread, and avoids a memory-order stall on loop exit. Pair with yieldNow.
pub cpuRelax -> void { unsafe { asm { "pause" } } }

// The whole of the time asked for, even across a signal.
pub sleepNs ns:long -> void { sysSleep(ns); }
pub sleepMs ms:long -> void { sysSleep(ms * 1000000); }

// ─── identity ───────────────────────────────────────────────────────────────

// The kernel task id of the calling thread.
pub threadId -> long { unsafe { return syscall0(Syscall.Gettid); } }

// Shared by every thread in the process.
pub processId -> long { unsafe { return syscall0(Syscall.Getpid); } }

// How many CPUs this process may run on (Rust's available_parallelism): what to size a pool of
// workers by. At least 1.
pub availableParallelism -> long {
    mask: [u8; 128];                      // room for 1024 CPUs
    n: long = 0;
    unsafe { n = syscall3(Syscall.SchedGetaffinity, 0, 128, &mask as long); }
    if (n <= 0) { return 1; }
    count: long = 0;
    for i in 0..n {
        b: long = mask[i] as long;
        while (b != 0) { count = count + (b & 1); b = b >> 1; }
    }
    if (count < 1) { return 1; }
    return count;
}

// ─── threads ────────────────────────────────────────────────────────────────
// One mmap per thread holds its control block, its TLS page and its stack:
//   [    +0]  the control words, named by `Ctl` below
//   [ +4096]  the thread's TLS page (its heap cache and its chain of armed `recover`s, set via
//             CLONE_SETTLS)
//   [ +8192]  a guard page, no access: a stack that overflows faults here instead of
//             overwriting the TLS page and the control words
//   [+12288..size]  the thread's stack (grows down)
//
// `Tid` and `Cancel` change while another thread reads them (the kernel writes `Tid`, `kill`
// writes `Cancel`), so every access to them is an atomic load or store: a body polling
// `shouldStop` in a loop reads memory each time round. The other words are written before the
// thread starts and only read after.
local enum Ctl: long {
    Tid,        // kernel tid; the kernel clears it to 0 on exit, which is what join waits on
    Cancel,     // kill sets it; the body polls shouldStop
    Fn,         // the thread function, read from here by the child
    Arg,        // the user argument from spawn
    Size        // the region's length in bytes: where the stack starts, and what join unmaps
}

local PAGE: long = 4096;
local HEAD: long = 12288;                // the control page, the TLS page, the guard page
pub DEFAULT_STACK: long = 57344;         // a 68 KiB region in all

local unsafe ctl r:long -> *long { return r as *long; }
local unsafe ctlWord r:long w:Ctl -> *long { return (r + 8 * (w as long)) as *long; }

// ─── the child side ─────────────────────────────────────────────────────────
// The kernel hands the child its region address in a register, so a thread body is
// `fn(ctrl:long)->void` and receives the raw control pointer. This is where the ABI leaks into
// the API.
//
// Unchecked: both accessors trust `ctrl` to be the live block spawn() passed in. A body handed
// any other long reads whatever is at that address.

// The argument given to spawn, typically a heap pointer to shared data.
pub threadArg ctrl:long -> long { unsafe { return ctl(ctrl)[Ctl.Arg]; } }
// True once kill() has asked this thread to stop; a body should poll it and return.
pub shouldStop ctrl:long -> bool { unsafe { return atomicLoad(ctlWord(ctrl, Ctl.Cancel)) != 0; } }

// Start fn(ctrl) on `region`'s stack with its own TLS. `rbx` survives the syscall into the
// child (callee-saved by the syscall ABI), and the child reads its function from the shared
// control block rather than a register or stack slot the kernel may not carry across clone.
// One `asm` block, since the child may run nothing compiled until it is on its own stack.
local unsafe threadClone region:long -> void {
    asm {
        in rbx region;                // ctrl -> rbx, survives clone into the child
        "mov rsi, [rbx + 32]"         // the Size word: the stack top is region + size
        "add rsi, rbx"
        "and rsi, -16"
        "sub rsi, 16"
        "mov r10, rbx"                // childTid ptr (the Tid word)
        "lea r8, [rbx + 4096]"        // TLS page (CLONE_SETTLS)
        "mov rdx, rbx"                // parentTid ptr
        "mov rdi, 0x3D0F00"           // VM|FS|FILES|SIGHAND|THREAD|SYSVSEM|PARENT_SETTID|CHILD_CLEARTID|SETTLS
        "mov eax, 56"                 // clone
        "syscall"
        "test rax, rax"
        "jnz .tcloneParent"
        "mov rdx, [rbx + 16]"         // CHILD: the Fn word
        "mov rax, rbx"                // arg0 = ctrl (Kiln passes arg0 in rax)
        "mov rdi, rbx"                // and in rdi, where a body built by LLVM (System V) reads it
        "call rdx"
        "mov eax, 60"                 // exit, this thread only
        "xor rdi, rdi"
        "syscall"
        ".tcloneParent:"
    }
}

// ─── the parent side ────────────────────────────────────────────────────────
// Plain data (Copy), so it can be stored and passed around, but a distinct type, so a bare
// `long` cannot be joined by accident.
pub struct Thread { ctrl: *u8 }

// Start `f(ctrl)` on a thread of its own, with a stack of DEFAULT_STACK bytes.
pub spawn f:fn(long)->void arg:long -> Thread { return spawnWithStack(f, arg, DEFAULT_STACK); }

// The same with the stack size chosen: deep recursion in the body wants more than the default,
// thousands of small workers less. Rounded up to whole pages, and at least one.
pub spawnWithStack f:fn(long)->void arg:long stackBytes:long -> Thread {
    stack: long = (stackBytes + PAGE - 1) / PAGE * PAGE;
    if (stack < PAGE) { stack = PAGE; }
    size: long = HEAD + stack;
    unsafe {
        region: long = syscall6(Syscall.Mmap, 0, size, 3, 0x22, -1, 0);   // RW, PRIVATE|ANON
        if (region < 0) { panic("spawn: cannot allocate thread stack (mmap failed)"); }
        syscall3(Syscall.Mprotect, region + 2 * PAGE, PAGE, 0);          // PROT_NONE
        w: *long = ctl(region);
        w[Ctl.Tid] = 0;               // the kernel fills this in, and clears it on exit
        w[Ctl.Cancel] = 0;
        w[Ctl.Fn] = f as long;
        w[Ctl.Arg] = arg;
        w[Ctl.Size] = size;
        threadClone(region);
        return Thread { ctrl: region as *u8 };
    }
}

methods Thread {
    // The kernel task id, or 0 once the thread has exited.
    id &self -> long { unsafe { return atomicLoad32(self.ctrl as *int) as long; } }   // the kernel writes 32 bits
    isRunning &self -> bool { return self.id() != 0; }
    // Cooperative: the body must poll shouldStop and return.
    kill &self -> void { unsafe { atomicStore(ctlWord(self.ctrl as long, Ctl.Cancel), 1); } }

    // Block until the thread finishes, then give its region back to the OS. The kernel clears
    // the Tid word and futex-wakes on exit, so this parks in the kernel rather than spinning.
    join &self -> void {
        unsafe {
            tid: *int = self.ctrl as *int;           // the kernel writes a 32-bit tid
            loop {
                t: int = atomicLoad32(tid);
                if (t == 0) { break; }
                syscall4(Syscall.Futex, tid as long, 0, t, 0);   // FUTEX_WAIT while it still reads t
            }
            syscall2(Syscall.Munmap, self.ctrl as long, ctl(self.ctrl)[Ctl.Size]);
        }
    }
}
