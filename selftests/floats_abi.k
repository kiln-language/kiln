// Floats as arguments and results: in xmm0-7 and counted apart from the integers, more than eight
// of them, mixed with integers, returned, as struct fields passed by value, in a Vec, an array,
// a tuple, through a fn value and a generic.
#include <stdlib::vec>
bits x:f64 -> long { r: long = 0; unsafe { asm { in rax x; out r rax; } } return r; }
struct P { x: f64, n: long, y: f32 }
mix a:long x:f64 b:long y:f32 c:f64 d:int -> f64 { return (a as f64) * x + (b as f64) + (y as f64) * c + (d as f64); }
ten a:f64 b:f64 c:f64 d:f64 e:f64 f:f64 g:f64 h:f64 i:f64 j:f64 k:long l:f32 -> f64 {
    return a + b * 2.0 + c * 3.0 + d * 4.0 + e * 5.0 + f * 6.0 + g * 7.0 + h * 8.0 + i * 9.0 + j * 10.0 + (k as f64) + (l as f64);
}
norm p:P -> f64 { return p.x * p.x + (p.y as f64) + (p.n as f64); }
twice f:fn(f64) -> f64 x:f64 -> f64 { return f(f(x)); }
half x:f64 -> f64 { return x / 2.0; }
pick<T> a:T b:T first:bool -> T { if (first) { return a; } return b; }
main -> int {
    bad: long = 0;
    if (mix(2, 1.5, 3, 0.5, 4.0, 1) != 9.0) { bad = bad | 1; }
    if (ten(1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 5, 0.5) != 60.5) { bad = bad | 2; }
    p: P = P { x: 3.0, n: 7, y: 0.5 };
    if (norm(p) != 16.5) { bad = bad | 4; }
    v: Vec<f64>;
    for i in 0..10 { v.push((i as f64) * 0.5); }
    s: f64 = 0.0;
    for x in v { s = s + x; }
    if (s != 22.5 || v.get(3) != 1.5) { bad = bad | 8; }
    arr: [f32; 4] = [1.0, 2.0, 3.0, 4.5];
    t: f32 = 0.0;
    for i in 0..4 { t = t + arr[i]; }
    if (t != 10.5) { bad = bad | 16; }
    tu: (f64, long, f32) = (2.5, 3, 0.25);
    if (tu.0 * (tu.1 as f64) + (tu.2 as f64) != 7.75) { bad = bad | 32; }
    if (twice(&half, 10.0) != 2.5) { bad = bad | 64; }
    if (pick(1.25, 2.5, false) != 2.5) { bad = bad | 128; }
    return bad as int;
}
