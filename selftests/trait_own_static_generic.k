// A static method of a trait this file owns, called on a generic type (`W.make(...)` with
// `methods W<T> for Make`): the instance's method carries the trait in its name, and the call
// reaches it, the instance read off the destination and off an argument. 3 + 4 + 20 = 27.
trait Make { make v:long -> Self; }
trait Size { size &self -> long; }
struct W<T> { v: T, n: long }
methods W<T> for Make { make v:long -> W<T> { w: W<T>; w.n = v; return w; } }
methods W<T> for Size { size &self -> long { return self.n * 10; } }
struct P { n: long }
methods P for Make { make v:long -> P { return P { n: v + 1 }; } }
main -> int {
    a: W<long> = W.make(3);
    b: P = P.make(3);
    c: W<P> = W.make(2);
    return (a.n + b.n + c.size()) as int;
}
