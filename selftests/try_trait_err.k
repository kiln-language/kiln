// `?` hands the residual to the return type's `fromResidual`: a Res's error is no Maybe's.
trait Try<T, R> { isBreak &self -> bool; output self -> T; residual self -> R; fromResidual r:R -> Self; }
trap -> never { unsafe { asm -> never { "ud2" } } }
enum Res<T, E> { Good(T), Bad(E) }
methods Res<T, E> for Try<T, E> {
    isBreak &self -> bool { match self { Bad(e) { return true; } _ { } } return false; }
    output self -> T { match self { Good(v) { return v; } _ { } } trap(); }
    residual self -> E { match self { Bad(e) { return e; } _ { } } trap(); }
    fromResidual e:E -> Res<T, E> { return Res.Bad(e); }
}
struct Absent { }
enum Maybe<T> { No, Yes(T) }
methods Maybe<T> for Try<T, Absent> {
    isBreak &self -> bool { match self { No { return true; } _ { } } return false; }
    output self -> T { match self { Yes(v) { return v; } _ { } } trap(); }
    residual self -> Absent { return Absent { }; }
    fromResidual a:Absent -> Maybe<T> { return Maybe.No; }
}
half n:long -> Res<long, long> { return Res.Good(n / 2); }
f n:long -> Maybe<long> { h: long = half(n)?; return Maybe.Yes(h); }
main -> long { return 0; }
