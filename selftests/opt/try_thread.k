// `?` through `Try` branches exactly as the `match` a person writes: `isBreak`'s bool is set to a
// constant on each path and tested once after the inlined body, and `flow.k` threads each of those
// edges straight to where the test sends it; the tag test `output` and `residual` repeat is then
// decided by the edge it is reached on. One compare in each function, and no call to the trap.
// The two implementations are written the way the standard library's Result and Option are meant
// to be (PORT.md, "Behaviour keyed on names", item 10: `output` tests the breaking variant first).
// ir-count: try_thread::stepTry jcc 1
// ir-count: try_thread::stepMatch jcc 1
// ir-lacks: try_thread::stepTry jz
// ir-lacks: try_thread::stepTry trap
// ir-lacks: try_thread::stepTry call try_thread::Outcome
// ir-count: try_thread::findTry jcc 1
// ir-count: try_thread::findMatch jcc 1
// ir-lacks: try_thread::findTry jz
// ir-lacks: try_thread::findTry trap
trait Try<T, R> { isBreak &self -> bool; output self -> T; residual self -> R; fromResidual r:R -> Self; }
trap -> never { unsafe { asm -> never { "ud2" } } }

enum Outcome<T, E> { Good(T), Bad(E) }
methods Outcome<T, E> for Try<T, E> {
    isBreak &self -> bool { match self { Bad(e) { return true; } _ { } } return false; }
    output self -> T { match self { Bad(e) { trap(); } Good(v) { return v; } } }
    residual self -> E { match self { Good(v) { trap(); } Bad(e) { return e; } } }
    fromResidual e:E -> Outcome<T, E> { return Outcome.Bad(e); }
}

struct Missing { }
enum Maybe<T> { Some(T), None }
methods Maybe<T> for Try<T, Missing> {
    isBreak &self -> bool { match self { None { return true; } _ { } } return false; }
    output self -> T { match self { None { trap(); } Some(v) { return v; } } }
    residual self -> Missing { match self { Some(v) { trap(); } None { return Missing { }; } } }
    fromResidual r:Missing -> Maybe<T> { return Maybe.None; }
}

half n:long -> Outcome<long, long> { if (n % 2 != 0) { return Outcome.Bad(n); } return Outcome.Good(n / 2); }
stepTry n:long -> Outcome<long, long> { h: long = half(n)?; return Outcome.Good(h + 1); }
stepMatch n:long -> Outcome<long, long> {
    match half(n) { Good(h) { return Outcome.Good(h + 1); } Bad(e) { return Outcome.Bad(e); } }
}

look n:long -> Maybe<long> { if (n > 10) { return Maybe.None; } return Maybe.Some(n * 3); }
findTry n:long -> Maybe<long> { v: long = look(n)?; return Maybe.Some(v - 1); }
findMatch n:long -> Maybe<long> {
    match look(n) { Some(v) { return Maybe.Some(v - 1); } None { return Maybe.None; } }
}

main -> int {
    match stepTry(8) { Good(v) { if (v != 5) { return 1; } } Bad(e) { return 2; } }
    match stepTry(7) { Good(v) { return 3; } Bad(e) { if (e != 7) { return 4; } } }
    match stepMatch(8) { Good(v) { if (v != 5) { return 5; } } Bad(e) { return 6; } }
    match findTry(4) { Some(v) { if (v != 11) { return 7; } } None { return 8; } }
    match findTry(12) { Some(v) { return 9; } None { } }
    match findMatch(12) { Some(v) { return 10; } None { } }
    return 0;
}
