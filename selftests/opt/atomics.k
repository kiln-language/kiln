// The atomics are one instruction each and stay where they are written. A wait on a flag keeps
// its atomic load in the loop, and a plain read beside it in the loop stays there too; a plain
// read of the word beside it after an atomic load is not taken from the read before it; a dropped
// result keeps its add, and two adds stay two. A call to a function holding an atomic ends what the
// caller knew of memory another thread can reach, as a call that writes it would.
// ir-after: atomics::spin atomic load .L0
// ir-after: atomics::spinRead ptrload .L0
// ir-count: atomics::twice ptrload 2
// ir-count: atomics::twice atomic load 1
// ir-count: atomics::twiceCall ptrload 2
// ir-count: atomics::bumps atomic add 2
// asm-count: main lock xadd 2
// asm-has: main lock cmpxchg
// asm-has: main xchg
pub unsafe builtin atomicLoad p:*long -> long;
pub unsafe builtin atomicStoreSeqCst p:*long v:long -> void;
pub unsafe builtin atomicCas p:*long expected:long desired:long -> long;
pub unsafe builtin atomicAdd p:*long delta:long -> long;

spin p:*long -> long {
    n: long = 0;
    unsafe { while (atomicLoad(p) != 0) { n = n + 1; } }
    return n;
}
spinRead p:*long -> long {
    n: long = 0;
    unsafe { while (p[1] + atomicLoad(p) == 7) { n = n + 1; } }
    return n;
}
twice p:*long -> long {
    unsafe {
        a: long = p[1];
        atomicLoad(p);
        return a + p[1];
    }
}
// Too big to copy into its two callers, so it stays a call, and its summary is its own.
waitBig p:*long n:long -> long {
    s: long = 0;
    for i in 0..n { s = s + i * 3; s = s ^ (s >> 2); s = s + (i & 5); s = s - (s >> 3); }
    for i in 0..n { s = s + i * 7; s = s ^ (s >> 1); s = s + (i | 9); s = s - (s >> 4); }
    unsafe { s = s + atomicLoad(p); }
    return s;
}
twiceCall p:*long -> long {
    unsafe {
        a: long = p[1];
        waitBig(p, 3);
        return a + p[1];
    }
}
bumps p:*long -> void { unsafe { atomicAdd(p, 1); atomicAdd(p, 1); } }
cas p:*long -> long { unsafe { return atomicCas(p, 1, 2); } }
seqst p:*long -> void { unsafe { atomicStoreSeqCst(p, 5); } }

main -> int {
    w: [long; 2] = [0, 3];
    unsafe {
        p: *long = &w[0] as *long;
        if (spin(p) != 0) { return 1; }
        if (spinRead(p) != 0) { return 6; }
        if (twice(p) != 6) { return 2; }
        if (twiceCall(p) != 6) { return 7; }
        if (waitBig(p, 0) != 0) { return 8; }
        bumps(p);
        if (w[0] != 2) { return 3; }
        if (cas(p) != 2 || w[0] != 2) { return 4; }
        seqst(p);
        if (w[0] != 5) { return 5; }
    }
    return 0;
}
