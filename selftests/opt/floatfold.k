// Float arithmetic on constants folds, exactly as the SSE instruction computes it: 0.1 + 0.2 is
// 0.30000000000000004 (bits 4599075939470750516), a NaN comparison folds to false, `-0.0` keeps
// its sign. Nothing that is not an identity for every input (`x + 0.0`, `x * 1.0`) is touched.
// ir-has: floatfold::f const 4599075939470750516
// ir-lacks: floatfold::f add
// ir-has: floatfold::g const 0
// ir-lacks: floatfold::g jcc
// ir-has: floatfold::keep add
bits x:f64 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r; }
f -> f64 { a: f64 = 0.1; b: f64 = 0.2; return a + b; }
g -> long { z: f64 = 0.0; n: f64 = z / z; if (n == n) { return 1; } return 0; }
keep x:f64 -> f64 { return x + 0.0; }
main -> int {
    if (bits(f()) != 4599075939470750516 || g() != 0 || bits(keep(-0.0)) != 0) { return 1; }
    return 0;
}
