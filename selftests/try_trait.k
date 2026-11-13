// `?` through the core trait `Try<T, R>` (declared here, as `stdlib::core` will declare it): any
// return type implementing it, a library's own Result-like and Option-like types included. The
// failure travels as the residual: `fromResidual` of the function's own return type builds the
// early result from it.
trait Try<T, R> {
    isBreak &self -> bool;
    output self -> T;
    residual self -> R;
    fromResidual r:R -> Self;
}
trap -> never { unsafe { asm -> never { "ud2" } } }

enum Res<T, E> { Good(T), Bad(E) }
methods Res<T, E> for Try<T, E> {
    isBreak &self -> bool { match self { Bad(e) { return true; } _ { } } return false; }
    output self -> T { match self { Good(v) { return v; } _ { } } trap(); }
    residual self -> E { match self { Bad(e) { return e; } _ { } } trap(); }
    fromResidual e:E -> Res<T, E> { return Res.Bad(e); }
}
// The absence carries nothing: its residual is a unit.
struct Absent { }
enum Maybe<T> { No, Yes(T) }
methods Maybe<T> for Try<T, Absent> {
    isBreak &self -> bool { match self { No { return true; } _ { } } return false; }
    output self -> T { match self { Yes(v) { return v; } _ { } } trap(); }
    residual self -> Absent { return Absent { }; }
    fromResidual a:Absent -> Maybe<T> { return Maybe.No; }
}
half n:long -> Res<long, long> { if (n % 2 != 0) { return Res.Bad(n); } return Res.Good(n / 2); }
quarter n:long -> Res<long, long> {
    h: long = half(n)?;                  // the rest of the block runs only when it is Good
    q: long = half(h)? + 0;
    return Res.Good(q);
}
firstDigit s:str -> Maybe<long> {
    if (s.len == 0) { return Maybe.No; }
    if (s[0] < 48 || s[0] > 57) { return Maybe.No; }
    return Maybe.Yes((s[0] - 48) as long);
}
sumDigits a:str b:str -> Maybe<long> { return Maybe.Yes(firstDigit(a)? + firstDigit(b)?); }
// An owning value moved out on the good path, released on the early one.
struct Box2 { v: long }
var gDrops: long = 0;
methods Box2 for Drop { drop &self -> void { gDrops = gDrops + 1; } }
mk n:long -> Res<Box2, long> { if (n < 0) { return Res.Bad(n); } return Res.Good(Box2 { v: n }); }
use n:long -> Res<long, long> { b: Box2 = mk(n)?; return Res.Good(b.v); }
main -> long {
    t: long = 0;
    match quarter(36) { Good(v) { t = t + v; } Bad(e) { return 1; } }      // 9
    match quarter(6) { Good(v) { return 2; } Bad(e) { t = t + e; } }       // 3 (half of 6 is odd)
    match sumDigits("7x", "8y") { Yes(v) { t = t + v; } No { return 3; } } // 15
    match sumDigits("7x", "") { Yes(v) { return 4; } No { } }
    match use(10) { Good(v) { t = t + v; } Bad(e) { return 5; } }          // 10, b released once
    match use(-1) { Good(v) { return 6; } Bad(e) { } }
    if (gDrops != 1) { return 7; }
    return t + 5;                                                           // 9 + 3 + 15 + 10 + 5 = 42
}
