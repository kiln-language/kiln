// A division or remainder by a constant keeps the constant on the instruction, where the emitter
// divides by multiplying; the constant itself is gone.
// ir-has: divconst::f div
// ir-has: divconst::f mod
// ir-lacks: divconst::f const 7
// ir-lacks: divconst::f const 1000
f x:long -> long { return x / 7 + x % 1000; }
main -> int {
    if (f(7007) != 1008 || f(-7007) != -1008) { return 1; }
    return 0;
}
