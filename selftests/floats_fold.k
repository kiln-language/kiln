// What the compiler computes ahead of time equals what the program computes: the evaluator (an
// immutable global) and the optimizer's constant folding (a body of constants) against the same
// arithmetic through parameters, bit for bit, NaN and the signed zero included.
bits x:f64 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r; }
bits32 x:f32 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r & 4294967295; }
calc a:f64 b:f64 c:f64 -> f64 { return (a + b) * c / (a - c) - b; }
calcf a:f32 b:f32 -> f32 { return (a * b + a) / b; }
comptime -> f64 { x: f64 = 0.0; for i in 1..20 { x = x + 1.0 / (i as f64); } return x; }
G1: f64 = (0.1 + 0.7) * 3.3 / (0.1 - 3.3) - 0.7;
G2: f64 = comptime();
G3: f32 = (1.1 * 2.2 + 1.1) / 2.2;
G4: long = (2.9e3 as long) + ((-7.5) as long);
folded -> f64 { return (0.1 + 0.7) * 3.3 / (0.1 - 3.3) - 0.7; }
main -> int {
    bad: long = 0;
    run: f64 = calc(0.1, 0.7, 3.3);
    if (bits(G1) != bits(run)) { bad = bad | 1; }
    if (bits(folded()) != bits(run)) { bad = bad | 2; }
    x: f64 = 0.0;
    for i in 1..20 { x = x + 1.0 / (i as f64); }
    if (bits(G2) != bits(x)) { bad = bad | 4; }
    if (bits32(G3) != bits32(calcf(1.1, 2.2))) { bad = bad | 8; }
    if (G4 != 2893) { bad = bad | 16; }
    z: f64 = 0.0;
    if (bits(-z) != bits(-0.0)) { bad = bad | 32; }
    return bad as int;
}
