// `inout` on a scalar: the caller lends its local with `&`, the callee reads and writes it where
// it lies. Forwarded as `x` or `&x`; on a field, an element, a float, a bool, a backed enum; in a
// trait's signature and its implementation, called through a bound; at compile time.
trait Step { advance &self inout n:long -> void; }
struct By { k: long }
methods By for Step { advance &self inout n:long -> void { n = n + self.k; } }
enum Mode: u8 { Off, On }
next inout x:u64 -> u64 {
    x = x * 6364136223846793005 + 1442695040888963407;
    return x >> 33;
}
inc inout n:long -> void { n += 1; }
twice inout n:long -> void { inc(&n); inc(n); }            // forwarded both ways
flip inout b:bool -> void { b = !b; }
half inout f:f64 -> void { f = f / 2.0; }
toggle inout m:Mode -> void { if (m == Mode.Off) { m = Mode.On; } else { m = Mode.Off; } }
drive<S: Step> s:S inout n:long -> void { s.advance(&n); }
struct P { a: long, b: long }
folded -> long { v: long = 5; twice(&v); return v; }
G: long = folded();                                       // 7
main -> int {
    s: u64 = 1;
    r1: u64 = next(&s);
    r2: u64 = next(&s);
    if (r1 == r2) { return 1; }
    n: long = 10;
    twice(&n);                                            // 12
    p: P = P { a: 1, b: 2 };
    inc(&p.b);                                            // 3
    xs: [long; 3] = [0, 0, 0];
    inc(&xs[1]); inc(&xs[1]);                             // 2
    on: bool = false;
    flip(&on);
    f: f64 = 9.0;
    half(&f);                                             // 4.5
    m: Mode = Mode.Off;
    toggle(&m);
    by: By = By { k: 5 };
    drive(by, &n);                                        // 17
    obj: Step = by;
    obj.advance(&n);                                      // 22 (through the trait object)
    if (!on || m != Mode.On || (f * 2.0) as long != 9) { return 2; }
    return (n + p.b + xs[1] + G) as int;                  // 22 + 3 + 2 + 7 = 34
}
