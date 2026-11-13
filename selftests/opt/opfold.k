// An operator a type implements folds like a built-in one once its body is inlined: a distinct
// type's `Add` and `Eq`, the casts to and from its base, and a backed enum's comparison. The
// whole of `f` and `g` is the constant they return.
// ir-has: opfold::f const 5
// ir-lacks: opfold::f add
// ir-lacks: opfold::f jz
// ir-lacks: opfold::f call
// ir-has: opfold::g const 7
// ir-lacks: opfold::g jcc
type Meters = distinct long;
methods Meters for Add<Meters> { add &self o:Meters -> Meters { return ((self as long) + (o as long)) as Meters; } }
methods Meters for Eq<Meters> { eq &self o:Meters -> bool { return (self as long) == (o as long); } }
enum Color: int { Red, Green, Blue }
f -> long {
    x: Meters = (2 as Meters) + (3 as Meters);
    y: Meters = (4 as Meters) + (1 as Meters);
    if (x == y) { return x as long; }
    return 0;
}
g -> long {
    c: Color = Color.Green;
    if (c == Color.Green) { return 7; }
    return 1;
}
main -> int {
    if (f() != 5 || g() != 7) { return 1; }
    return 0;
}
