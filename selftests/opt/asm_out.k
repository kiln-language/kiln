// An `asm` block whose one output goes to a local nothing else pins writes the local's temp, not
// its slot (`Opt.promoteLocals`, `asmOutName`): a float's bits move into a general register and
// back with `movq`, with no store to the frame and no load back, and the small functions that do
// it are copied into their caller.
// asm-lacks: asm_out::abs [rbp
// asm-lacks: asm_out::abs call
// asm-has: asm_out::abs movq
local bitsOf x:f64 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local ofBits b:long -> f64 { r: f64 = 0.0; unsafe { asm { in rax b; out r rax; } } return r; }
abs x:f64 -> f64 { return ofBits(bitsOf(x) & 0x7FFFFFFFFFFFFFFF); }
main -> int {
    f: fn(f64) -> f64 = &abs;
    if (f(0.0 - 2.5) != 2.5 || f(1.5) != 1.5) { return 1; }
    if (bitsOf(f(0.0 - 0.0)) != 0) { return 2; }
    if (bitsOf(1.0) != 0x3FF0000000000000) { return 3; }
    return 0;
}
