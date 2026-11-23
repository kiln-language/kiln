#include <stdlib::{io, vec}>

// A closure inside a generic function or method, stamped at a struct type argument. Its capture
// struct is an instance whose name ends in that struct's (`m::$closure0_7_m::P`); it is still a
// closure's, and its captures are still the parser's.

viaBound<F: Fn() -> void> f:F -> void { f(); }
viaObj f:Fn() -> void -> void { f(); }

struct P { x: long }
struct Pair<T> { a: T, b: T }
struct Tree { items: Vec<long>, count: long }

// a captured `T` written through the closure: by pointer at a scalar, by pointer at a struct
pick<T: Copy> a:T b:T -> T { r: T = a; viaBound(|| { r = b; }); return r; }

methods Pair<T> {
    // `self` captured in a generic type's method, swapped through a trait-object closure
    swapIn &self -> void { viaObj(|| { t: T = self.a; self.a = self.b; self.b = t; }); }
}

// nested closures in a generic function, the inner one writing what the outer captured
deep<T: Copy> v:T -> T { out: T = v; viaObj(|| { viaBound(|| { out = v; }); }); return out; }

// a captured owning struct read through a closure at a struct argument
sizeOf<T> t:&T n:long -> long { s: long = 0; viaBound(|| { s = n * 2; }); return s; }

main -> long {
    one: long = 1;
    n: long = pick(one, 2);
    p: P = pick(P { x: 3 }, P { x: 4 });
    if (n != 2 || p.x != 4) { return 1; }
    b: Pair<long> = Pair { a: 3, b: 4 };
    c: Pair<P> = Pair { a: P { x: 1 }, b: P { x: 2 } };
    c.swapIn();
    b.swapIn();
    if (c.a.x != 2 || c.b.x != 1 || b.a != 4 || b.b != 3) { return 2; }
    q: P = deep(P { x: 9 });
    five: long = 5;
    if (q.x != 9 || deep(five) != 5) { return 3; }
    t: Tree = Tree { items: vec![1, 2], count: 2 };
    if (sizeOf(&t, 21) != 42) { return 4; }
    println("closure_generic_struct");
    return 0;
}
