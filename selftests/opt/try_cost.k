// `?` through `Try` costs what the match a person writes does: the four small methods inline,
// and none is called.
// ir-lacks: try_cost::step isBreak
// ir-lacks: try_cost::step output
// ir-lacks: try_cost::step residual
// ir-lacks: try_cost::step fromResidual
trait Try<T, R> { isBreak &self -> bool; output self -> T; residual self -> R; fromResidual r:R -> Self; }
trap -> never { unsafe { asm -> never { "ud2" } } }
enum Res<T, E> { Good(T), Bad(E) }
methods Res<T, E> for Try<T, E> {
    isBreak &self -> bool { match self { Bad(e) { return true; } _ { } } return false; }
    output self -> T { match self { Good(v) { return v; } _ { } } trap(); }
    residual self -> E { match self { Bad(e) { return e; } _ { } } trap(); }
    fromResidual e:E -> Res<T, E> { return Res.Bad(e); }
}
half n:long -> Res<long, long> { if (n % 2 != 0) { return Res.Bad(n); } return Res.Good(n / 2); }
step n:long -> Res<long, long> { h: long = half(n)?; return Res.Good(h + 1); }
main -> int {
    match step(8) { Good(v) { if (v != 5) { return 1; } } Bad(e) { return 2; } }
    match step(7) { Good(v) { return 3; } Bad(e) { if (e != 7) { return 4; } } }
    return 0;
}
