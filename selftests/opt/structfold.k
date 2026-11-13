// A small Copy struct's operator folds too: the `add` returning a `V2` is inlined (an aggregate
// result is a parameter like any other), the fields stored into the struct it builds are
// forwarded through the block copies into `c`, and what reads them is constant.
// ir-has: structfold::f const 33
// ir-lacks: structfold::f call
// ir-has: structfold::eqv const 1
// ir-lacks: structfold::eqv jz
struct V2 { x: long, y: long }
methods V2 for Add<V2> { add &self o:V2 -> V2 { return V2 { x: self.x + o.x, y: self.y + o.y }; } }
methods V2 for Eq<V2> { eq &self o:V2 -> bool { return self.x == o.x && self.y == o.y; } }
f -> long {
    a: V2 = V2 { x: 1, y: 2 };
    b: V2 = V2 { x: 10, y: 20 };
    c: V2 = a + b;
    return c.x + c.y;
}
eqv -> long {
    a: V2 = V2 { x: 1, y: 2 };
    b: V2 = V2 { x: 1, y: 2 };
    if (a == b) { return 1; }
    return 0;
}
main -> int {
    if (f() != 33 || eqv() != 1) { return 1; }
    return 0;
}
