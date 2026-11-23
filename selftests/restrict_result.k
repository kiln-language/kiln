// A borrow a call hands back, written through by the caller: the result points into what the
// call was handed, a borrowed parameter of the caller. The callees hold a loop and have two
// callers, so none is copied into its caller. Each check reads a field, writes 5 into it through
// the result and reads it again (1 + 5). Exits with the number of the first check that fails.
#include <stdlib::{io, vec}>

struct In { x: long, y: long }
struct P { a: long, inn: In }
struct Bag { items: Vec<In>, n: long }

var gDepth: long = 1;

methods P {
    inner &self k:long -> &In {
        s: long = 0;
        for i in 0..k { s += i * self.a; }
        if (s > 100) { println("inner {}", s); }
        return self.inn;
    }
}

// A method on the parameter.
viaMethod inout p:P n:long -> long {
    if (n > 0) { return viaMethod(&p, n - 1); }
    t: long = p.inn.x;
    p.inner(3).x = 5;
    return t + p.inn.x;
}

// The same one call further down: the callee's summary must say it writes its parameter, since
// what it writes through is what a call handed back.
writesThrough inout p:P k:long -> void {
    s: long = 0;
    for i in 0..k { s += i; }
    p.inner(3).x = 5 + s - s;
}
twoLevels inout p:P n:long -> long {
    if (n > 0) { return twoLevels(&p, n - 1); }
    t: long = p.inn.x;
    writesThrough(&p, 2);
    return t + p.inn.x;
}

// A function reached through a fn value.
innerOf read p:P k:long -> &In {
    s: long = 0;
    for i in 0..k { s += i * p.a; }
    if (s > 100) { println("innerOf {}", s); }
    return p.inn;
}
viaValue inout p:P f:fn(P, long) -> &In n:long -> long {
    if (n > 0) { return viaValue(&p, f, n - 1); }
    t: long = p.inn.x;
    f(p, 3).x = 5;
    return t + p.inn.x;
}

// An element of a vector the parameter holds, through a method on the parameter.
methods Bag {
    item &self i:long -> &In {
        s: long = 0;
        for k in 0..i { s += k; }
        if (s > 100) { println("item {}", s); }
        return self.items[i];
    }
}
viaElement inout b:Bag n:long -> long {
    if (n > 0) { return viaElement(&b, n - 1); }
    t: long = b.items[0].x;
    b.item(0).x = 5;
    return t + b.items[0].x;
}

main -> int {
    x: P = P { a: 1, inn: In { x: 1, y: 2 } };
    r: long = viaMethod(&x, gDepth);
    println("{}", r);
    if (r != 6) { return 1; }
    if (x.inner(2).y != 2) { return 2; }
    x.inn.x = 1;
    r = viaValue(&x, &innerOf, gDepth);
    println("{}", r);
    if (r != 6) { return 3; }
    if (innerOf(x, 1).y != 2) { return 4; }
    b: Bag = Bag { items: vec![], n: 0 };
    b.items.push(In { x: 1, y: 2 });
    r = viaElement(&b, gDepth);
    println("{}", r);
    if (r != 6) { return 5; }
    if (b.item(0).y != 2) { return 6; }
    x.inn.x = 1;
    r = twoLevels(&x, gDepth);
    println("{}", r);
    if (r != 6) { return 7; }
    writesThrough(&x, 1);
    if (x.inn.x != 5) { return 8; }
    return 0;
}
