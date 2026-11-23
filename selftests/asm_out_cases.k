#include <stdlib::recover>

// An `asm` block's one output into a local: written straight into the local's temp where nothing
// else pins it (`Opt.promoteLocals`, `asmOutName`), into its slot where something does. A
// `recover` whose handler reads the local the block wrote, a local lent to a call before and
// after the block, blocks in loops, and words moved in and out of general and `xmm` registers.

local bitsOf x:f64 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local ofBits b:long -> f64 { r: f64 = 0.0; unsafe { asm { in rax b; out r rax; } } return r; }
local viaXmm b:long -> long { r: long = 0; unsafe { asm { in rax b; "movq xmm1, rax" out r xmm1; } } return r; }

var gDepth: long = 3;
dive n:long -> long {
    if (n == 0) { unsafe { raise(); } }
    return dive(n - 1) + 1;
}

// The handler reads what the block wrote before the call that raised.
caught seed:long -> long {
    w: long = 0;
    unsafe {
        recover {
            asm { in rax seed; "add rax, 5" out w rax; }
            w = w + dive(gDepth);
        } else {
            w = w * 2;
        }
    }
    return w;
}

bump inout x:long -> void { x = x + 1; }

// Lent to a call before the block and after it.
lent seed:long -> long {
    v: long = seed;
    bump(&v);
    unsafe { asm { in rax v; "lea rcx, [rax + 10]" out v rcx; } }
    bump(&v);
    return v;
}

// A block in a loop, its output read the next time round.
spin n:long -> long {
    acc: long = 1;
    for i in 0..n {
        unsafe { asm { in rax acc; in rcx i; "imul rax, rax, 3" "add rax, rcx" out acc rax; } }
    }
    return acc;
}

// A float halved through its bits each time round: one less in the exponent.
halves n:long -> f64 {
    x: f64 = 1024.0;
    for i in 0..n { x = ofBits(bitsOf(x) - 0x0010000000000000); }
    return x;
}

main -> int {
    if (caught(10) != 30) { return 1; }
    if (lent(5) != 17) { return 2; }
    if (spin(4) != 99) { return 3; }
    if (halves(3) != 128.0) { return 4; }
    if (viaXmm(0x123456789) != 0x123456789) { return 5; }
    if (bitsOf(ofBits(77)) != 77) { return 6; }
    return 0;
}
