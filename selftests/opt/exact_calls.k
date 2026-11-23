// A value live across no call keeps a caller-saved register though a call lies inside its range
// (`RegAlloc.liveAcross`): every call here is followed by a return, so the five values need no
// callee-saved register, and nothing is pushed to keep one or written to the frame.
// asm-lacks: exact_calls::pick push r12
// asm-lacks: exact_calls::pick [rbp
var gN: long = 0;
// A loop: never copied into its callers.
note x:long -> void { for k in 0..x { gN = gN + k; } }
pick x:long y:long z:long w:long v:long -> long {
    if (x == 3) { note(y); return 0; }
    if (y == 4) { note(z); return 1; }
    return x * y + z * w + v;
}
main -> int {
    // Through a fn value, so `pick` is its own function and not copied into `main`.
    f: fn(long, long, long, long, long) -> long = &pick;
    if (f(1, 2, 3, 4, 5) != 19) { return 1; }
    if (f(3, 2, 3, 4, 5) != 0 || gN != 1) { return 2; }
    if (f(1, 4, 3, 4, 5) != 1 || gN != 4) { return 3; }
    return 0;
}
