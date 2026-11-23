// The atomic builtins, declared here as the standard library declares them: each one instruction,
// on an eight-byte word and on a four-byte one, the same at run time and in the evaluator (a
// global folded through them), with a result read or dropped, and with operands crowded out of
// registers.
pub unsafe builtin atomicLoad p:*long -> long;
pub unsafe builtin atomicStore p:*long v:long -> void;
pub unsafe builtin atomicStoreSeqCst p:*long v:long -> void;
pub unsafe builtin atomicSwap p:*long v:long -> long;
pub unsafe builtin atomicCas p:*long expected:long desired:long -> long;
pub unsafe builtin atomicAdd p:*long delta:long -> long;
pub unsafe builtin atomicLoad32 p:*int -> int;
pub unsafe builtin atomicStore32 p:*int v:int -> void;
pub unsafe builtin atomicStoreSeqCst32 p:*int v:int -> void;
pub unsafe builtin atomicSwap32 p:*int v:int -> int;
pub unsafe builtin atomicCas32 p:*int expected:int desired:int -> int;
pub unsafe builtin atomicAdd32 p:*int delta:int -> int;

struct Cell { pad: long, n: long, k: int, m: int }

run -> long {
    c: Cell = Cell { pad: 7, n: 10, k: -5, m: 0 };
    unsafe {
        p: *long = &c.n as *long;
        q: *int = &c.k as *int;
        if (atomicLoad(p) != 10) { return 1; }
        atomicStore(p, 20);
        if (c.n != 20) { return 2; }
        atomicStoreSeqCst(p, 21);
        if (atomicSwap(p, 30) != 21 || c.n != 30) { return 3; }
        if (atomicCas(p, 99, 40) != 30 || c.n != 30) { return 4; }      // not 99: nothing stored
        if (atomicCas(p, 30, 40) != 30 || c.n != 40) { return 5; }      // 30: it takes
        if (atomicAdd(p, -3) != 40 || c.n != 37) { return 6; }
        atomicAdd(p, 0);                                                // the old value dropped
        if (atomicLoad32(q) != -5) { return 7; }
        atomicStore32(q, -7);
        if (c.k != -7 || c.m != 0 || c.pad != 7) { return 8; }          // the neighbours untouched
        atomicStoreSeqCst32(q, 2147483647);
        if (atomicAdd32(q, 1) != 2147483647 || c.k != -2147483647 - 1) { return 9; }   // wraps at 32 bits
        if (atomicSwap32(q, -1) != -2147483647 - 1 || c.k != -1) { return 10; }
        if (atomicCas32(q, -1, 5) != -1 || c.k != 5 || c.m != 0) { return 11; }
        if (atomicCas32(q, -1, 6) != 5 || c.k != 5) { return 12; }
        return c.n + c.k;                                               // 37 + 5
    }
}

// Sixteen values live across the atomics, so some of their operands have no register.
crowded seed:long -> long {
    c: Cell = Cell { pad: 0, n: seed, k: 0, m: 0 };
    a0: long = seed + 1; a1: long = seed * 3; a2: long = seed - 4; a3: long = seed ^ 5;
    a4: long = seed + 6; a5: long = seed * 7; a6: long = seed - 8; a7: long = seed ^ 9;
    a8: long = seed + 10; a9: long = seed * 11; b0: long = seed - 12; b1: long = seed ^ 13;
    b2: long = seed + 14; b3: long = seed * 15; b4: long = seed - 16; b5: long = seed ^ 17;
    r: long = 0;
    unsafe {
        p: *long = &c.n as *long;
        r = atomicCas(p, seed, a9);                     // takes: c.n = seed * 11
        r = r + atomicCas(p, a9, b3);                   // takes: c.n = seed * 15
        r = r + atomicSwap(p, a5) + atomicAdd(p, a1);   // c.n = seed * 10
        r = r + atomicLoad(p);
    }
    return r + a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + b0 + b1 + b2 + b3 + b4 + b5;
}

FOLDED: long = run();          // computed by the compiler, through the evaluator's atomics
FOLDED_CROWD: long = crowded(3);

main -> long {
    if (FOLDED != 42) { return 100 + FOLDED; }
    x: long = run();
    if (x != 42) { return 60 + x; }
    if (crowded(3) != FOLDED_CROWD) { return 50; }
    return 42;
}
