// A method may declare type parameters of its own, in a plain block or a generic one, static or
// on `&self`: each call stamps it, the parameters inferred from the arguments and the destination
// as a generic function's are, and a bound on one is what the body may call.
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::string>

trait ToAddr { toAddr &self -> long; }
methods long for ToAddr { toAddr &self -> long { return self * 10; } }
struct Host { n: long }
methods Host for ToAddr { toAddr &self -> long { return self.n + 1000; } }

struct Cfg { n: long }
methods Cfg for Default { new -> Cfg { return Cfg { n: 77 }; } }

struct L { port: long }
methods L {
    bind<A: ToAddr> a:A -> L { return L { port: a.toAddr() }; }
    with<B> &self b:B f:fn(B) -> long -> long { return self.port + f(b); }
    pairUp<X, Y> x:X y:Y -> (X, Y) { return (x, y); }
    make<D: Default> &self -> D { return D.new(); }
    build<D: Default> -> D { return D.new(); }
}
twice x:long -> long { return x * 2; }
dbl x:long -> String { s: String = stringOf("v"); s.pushLong(x * 2); return s; }
gt lim:long x:long -> bool { return x > lim; }
isLen s:str x:long -> bool { return x == s.len; }

methods Vec<T> {
    mapTo<U> &self f:fn(T) -> U -> Vec<U> {
        out: Vec<U>;
        out.reserve(self.len());
        for x in self { out.push(f(x)); }
        return out;
    }
    countIf<P> &self ctx:P f:fn(P, T) -> bool -> long {
        c: long = 0;
        for x in self { if (f(ctx, x)) { c = c + 1; } }
        return c;
    }
}

main -> int {
    l: L = L.bind(5 as long);
    m: L = L.bind(Host { n: 7 });
    if (l.port != 50 || m.port != 1007) { return 1; }
    if (l.with(21, &twice) != 92) { return 2; }
    p: (long, String) = L.pairUp(3, stringOf("x"));
    if (p.0 != 3 || p.1.len != 1) { return 3; }
    c: Cfg = l.make();
    d: Cfg = L.build();
    if (c.n + d.n != 154) { return 4; }
    v: Vec<long> = vec![1, 5, 9, 3];
    w: Vec<String> = v.mapTo(&dbl);
    if (w.len() != 4 || w[2].len != 3) { return 5; }
    if (v.countIf(2 as long, &gt) != 3 || v.countIf("abc", &isLen) != 1) { return 6; }
    println("ok");
    return 0;
}
