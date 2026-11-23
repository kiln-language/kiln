// A value live across calls, in a caller-saved register with a home in the frame, is written to
// its home before the first call after it changes (`Emitter.storeBefore`), not wherever it is
// written: `bump`, written every turn of the inner loop, which makes no call, is stored once per
// turn of the outer one, before its call. Five stores in all: two values left in the frame, each
// stored where it is made, two homed ones before the call, and the fn value parked for the call
// (seven with `--no-sink-homes`).
// The call goes through a fn value, which may change every caller-saved register: called
// directly, `note` would leave most of them alone and the values would need no home at all.
// asm-count: sink_homes::walk mov [rbp 5
var gK: long = 3;
// A loop called from two places, so never copied into its callers.
note x:long -> long {
    s: long = 0;
    for k in 0..x { s = s + k * gK; }
    return s;
}
var gNote: fn(long) -> long = &note;
walk n:long -> long {
    a: long = gK;
    b: long = gK * 2;
    c: long = gK * 3;
    d: long = gK * 5;
    e: long = gK * 7;
    bump: long = 0;
    for i in 0..n {
        for j in 0..n { bump = bump + j * i; }
        a = a + gNote(bump);
    }
    return a + b + c + d + e + bump;
}
main -> int {
    p: fn(long) -> long = &walk;
    if (p(4) != 2484) { return 1; }
    if (note(3) != 9) { return 2; }
    return 0;
}
