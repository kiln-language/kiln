// `methods<T: Integer> T for X`: one implementation for every integer type, read once per type
// with `T` standing for it; `Float` the same for f32 and f64. Through methods, a bound, `T` as a
// parameter's type, a cast and a static method. 6 + 10 + 4 + 18 + 7 + 3 + 9 + 1 + 1 = 59.
pub trait Twice { twice &self -> long; same &self other:Self -> bool; zero -> Self; }
methods<T: Integer> T for Twice {
    twice &self -> long { return (self as long) * 2; }
    same &self other:T -> bool { return (self as long) == (other as long); }
    zero -> T { return 0 as T; }
}
trait Halve { half &self -> long; }
methods<F: Float> F for Halve { half &self -> long { return (self / (2.0 as F)) as long; } }
viaBound<T: Twice> x:T -> long { return x.twice(); }
main -> int {
    a: u8 = 3;
    b: i16 = 5;
    c: char = 2 as char;
    d: u64 = 9;
    t: long = a.twice() + b.twice() + c.twice() + viaBound(d) + viaBound(7 as int) / 2;
    e: f64 = 6.5;
    g: f32 = 18.0;
    t = t + e.half() + g.half();
    if ((4 as u32).same(4 as u32)) { t = t + 1; }
    z: long = long.zero();
    if (z == 0) { t = t + 1; }
    return t as int;
}
