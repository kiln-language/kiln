// A global initialized by a bare float literal held 0.0 (the evaluator stored only an integer
// literal's value). Every global here must read back as written: 1 + 2 + 4 + 8 + 16 = 31.
G: f64 = 3.5;
H: f64 = 1.0 + 2.5;
K: f32 = 1.5;
N: f64 = -2.25;
var V: f64 = 4.5;
main -> int {
    r: long = 0;
    if (G == 3.5) { r = r + 1; }
    if (H == 3.5) { r = r + 2; }
    if (K == 1.5) { r = r + 4; }
    if (N == -2.25) { r = r + 8; }
    if (V == 4.5) { r = r + 16; }
    return r as int;
}
