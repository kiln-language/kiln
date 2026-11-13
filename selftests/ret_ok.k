// What a `return` may hand back: the declared type, a widening, a literal that fits, a struct
// literal of a generic type aimed at the declared instance (even a different one than the
// method's own), a generic function's T, a closure's declared result, `?`'s early return, and a
// void call from a void function.
#include <stdlib::{core, result, option}>
struct Pair<A, B> { a: A, b: B }
methods Pair<A: Copy, B: Copy> {
    swapped &self -> Pair<B, A> { return Pair { a: self.b, b: self.a }; }
    same &self -> Pair<A, B> { return Pair { a: self.a, b: self.b }; }
}
widen x:int -> long { return x; }
small -> u8 { return 200; }
narrowed x:long -> int { return x as int; }
ident<T> x:T -> T { return x; }
half x:long -> Result<long, long> { if (x % 2 != 0) { return Result.Err(x); } return Result.Ok(x / 2); }
quarter x:long -> Result<long, long> { h: long = half(x)?; return half(h); }
var gHits: long = 0;
bump -> void { gHits = gHits + 1; }
twice -> void { bump(); return bump(); }
main -> long {
    p: Pair<long, int> = Pair { a: 7, b: 9 };
    s: Pair<int, long> = p.swapped();
    t: Pair<long, int> = p.same();
    f: Fn(long) -> long = |v: long| -> long { return v + 1; };
    twice();
    q: Result<long, long> = quarter(12);
    total: long = s.a + s.b + t.a + widen(3) + small() + narrowed(4) + ident(5) + f(1) + gHits + q.unwrapOr(0);
    return total - 200;     // 9 + 7 + 7 + 3 + 200 + 4 + 5 + 2 + 2 + 3 = 242 -> 42
}
