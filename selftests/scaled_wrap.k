// An index that is a narrow shift: `i << 2` on an `int` wraps at 32 bits, so with i = 2^30 it is
// 0, and that 0 is what the bounds check passes. The access must read element 0 too, not
// `[A + i*4]` four gigabytes on: only a 64-bit shift or multiply becomes an addressing mode's scale.

var A: [u8; 16];
var I: [int; 16];
var S: [int; 2];
var U: [u32; 1];

pickA i:int -> long { return A[i << 2] as long; }
pickI j:int -> long { return I[j << 3] as long; }
pickU u:u32 -> long { return A[u << 2] as long; }
pickL i:long -> long { return A[i << 2] as long; }

main -> long {
    A[0] = 7;
    A[12] = 3;
    I[0] = 9;
    S[0] = 1073741824;
    S[1] = 536870912;
    U[0] = 1073741824;
    if (pickA(S[0]) != 7) { return 1; }
    if (pickI(S[1]) != 9) { return 2; }
    if (pickU(U[0]) != 7) { return 3; }
    if (pickL(3) != 3) { return 4; }
    return 0;
}
