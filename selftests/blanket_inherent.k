// `methods<T: Integer> T { ... }`: inherent methods for every integer type, read once per type
// with `T` standing for it, as the trait blankets are; `Signed`, `Unsigned` and `Float` too. A
// method, one taking a `T`, a static one. 42 + 10 + 7 + 3 + 2 + 1 + 1 + 1 = 67.
methods<T: Integer> T {
    twice &self -> long { return (self as long) * 2; }
    clampTo &self hi:T -> T { if (self > hi) { return hi; } return self; }
    one -> T { return 1 as T; }
}
methods<S: Signed> S { flip &self -> long { return 0 - (self as long); } }
methods<U: Unsigned> U { low &self -> long { return (self as long) & 3; } }
methods<F: Float> F { half &self -> F { return self / (2.0 as F); } }
main -> int {
    x: long = 21;
    b: u8 = 200;
    i: i16 = -7;
    u: u32 = 11;
    t: long = x.twice() + (x.clampTo(10) as long) + i.flip() + u.low();
    if (b.clampTo(250) == 200 && (b.clampTo(9) as long) == 9) { t = t + 2; }
    if (int.one() == 1 && u64.one() == 1) { t = t + 1; }
    f: f64 = 5.0;
    g: f32 = 3.0;
    if (f.half() == 2.5) { t = t + 1; }
    if (g.half() == 1.5) { t = t + 1; }
    return t as int;
}
