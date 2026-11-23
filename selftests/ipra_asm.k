#include <stdlib::{atomic, float, fmt, mem, process, result, string, thread, vec}>

// What a function holding an `asm` block may change is read off its lines like any other's
// (relax.k): every register they name, and what the instructions in its table write without
// naming (`rep stosb`'s rdi and rcx, `syscall`'s rcx and r11, `cmpxchg`'s rax); a line it does
// not know, a call through a register and a jump that leaves make it change anything. Each shape
// of `asm` the library has is reached here through a small function, and `keep` holds a dozen
// values across a call to each: an atomic on a byte (`xchg`, `lock xadd`, `lock cmpxchg`), a
// square root through xmm0, `memset`, the allocator's thread-local free lists, a thread started
// and joined (`clone` and a call through rdx), a program run (`vfork` and `execve`), a float
// formatted, and `pause`, `sched_yield` and `gettid`. And `cpuid`, which is not in the table and
// writes rbx and rcx: the function holding it may change anything.

var gSink: long = 0;
var gByte: Atomic<u8> = Atomic { value: 3 };
var gBuf: [u8; 64];
var gDone: long = 0;

atom n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    a: u8 = gByte.swap((s & 63) as u8);
    b: u8 = gByte.add(2);
    c: u8 = gByte.cas(b + 2, 7);
    return s + (a as long) + (b as long) + (c as long);
}
root n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    return (((s * s) as f64).sqrt()) as long;
}
fill n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    unsafe { memset(&gBuf as long, s & 127, (s & 31) + 1); }
    return s + (gBuf[0] as long);
}
grow n:long -> long {
    v: Vec<long> = vec![];
    for i in 0..(n & 7) + 20 { v.push(i * n); }
    return v.len() + v.get(3);
}
work ctrl:long -> void { gDone = gDone + threadArg(ctrl); }
spawnJoin n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    t: Thread = spawn(&work, s);
    t.join();
    return gDone;
}
run n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    args: Vec<str> = vec![];
    r: Result<ExitStatus, long> = runProcess("/bin/true", args);
    match r { Ok(st) { if (st.success()) { return s; } } Err(e) { } }
    return 0 - 1;
}
show n:long -> long {
    o: String = format("{}", (n as f64) * 0.5);
    return o.len();
}
idle n:long -> long {
    s: long = n;
    for i in 0..(n & 1) + 1 { s = s + i; }
    cpuRelax();
    yieldNow();
    return s + (threadId() & 0);
}
// The block first: nothing after a line the table does not know is read, so what the loop after
// it writes counts only because the function is taken to change everything.
cpu n:long -> long {
    z: long = 0;
    a: long = 0;
    unsafe { asm { in rax z; in rcx z; "cpuid" out a rax; } }
    p: long = n + (a & 0); q: long = p * 3 + 1; r: long = q * 5 + p; t: long = r * 7 + q;
    u: long = t * 11 + r; w: long = u * 13 + t;
    for i in 0..(n & 1) + 1 { p = p + i; }
    return (p ^ q ^ r ^ t ^ u ^ w) & 65535;
}

keep k:long -> long {
    v1: long = gSink + k + 1; v2: long = gSink + k * 2 + 2; v3: long = gSink + k * 3 + 3;
    v4: long = gSink + k * 4 + 4; v5: long = gSink + k * 5 + 5; v6: long = gSink + k * 6 + 6;
    v7: long = gSink + k * 7 + 7; v8: long = gSink + k * 8 + 8; v9: long = gSink + k * 9 + 9;
    v10: long = gSink + k * 10 + 10; v11: long = gSink + k * 11 + 11; v12: long = gSink + k * 12 + 12;
    r: long = atom(k) + v1;
    r = r + root(k) + v2 * 2;
    r = r + fill(k) + v3 * 3;
    r = r + grow(k) + v4 * 4;
    r = r + spawnJoin(k) + v5 * 5;
    r = r + run(k) + v6 * 6;
    r = r + show(k) + v7 * 7;
    r = r + idle(k) + v8 * 8;
    r = r + cpu(k) + v9;
    return r + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9 * 9 + v10 * 10 + v11 * 11 + v12 * 12;
}

// A second caller of each, so none is copied into `keep`.
again k:long -> long { return atom(k) + root(k) + fill(k) + grow(k) + spawnJoin(k) + run(k) + show(k) + idle(k) + cpu(k); }

main -> long {
    gSink = root(0);
    if (again(1) != 20553) { return 9; }
    if (keep(5) != 21869) { return 1; }
    if (keep(12) != 17023) { return 2; }
    return 0;
}
