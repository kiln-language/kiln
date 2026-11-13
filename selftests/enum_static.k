// `E.name(...)` is a static method of the enum when `name` is not one of its variants: for a sum
// type, generic or not, as for an enum of named integers. A variant keeps its name.
#include <stdlib::io>
#include <stdlib::option>
#include <stdlib::result>

enum SA { V4(long), V6(long, long), Unix }
methods SA {
    parse s:str -> Option<SA> {
        if (s.len == 0) { return Option.None; }
        if (s.len > 3) { return Option.Some(SA.V6(s.len, 1)); }
        return Option.Some(SA.V4(s.len));
    }
    unix -> SA { return SA.Unix; }
    port &self -> long { match self { V4(p) { return p; } V6(a, b) { return a + b; } Unix { return 0; } } }
}
enum Color: int { Red, Green }
methods Color { pick n:long -> Color { if (n > 0) { return Color.Green; } return Color.Red; } }

// On a generic sum type: the instance is inferred from the arguments, or from the destination.
methods Option<T> {
    fromFlag f:bool v:T -> Option<T> { if (f) { return Option.Some(v); } return Option.None; }
    nothing -> Option<T> { return Option.None; }
}
methods Result<T, E> {
    okIf c:bool v:T e:E -> Result<T, E> { if (c) { return Result.Ok(v); } return Result.Err(e); }
}

main -> int {
    a: Option<SA> = SA.parse("abc");
    match a { Some(s) { if (s.port() != 3) { return 1; } } None { return 2; } }
    b: Option<SA> = SA.parse("abcdef");
    match b { Some(s) { if (s.port() != 7) { return 3; } } None { return 4; } }
    if (SA.parse("").isSome()) { return 5; }
    u: SA = SA.unix();
    if (u.port() != 0) { return 6; }
    v: SA = SA.V4(9);                       // still the variant
    if (v.port() != 9) { return 7; }
    if (Color.pick(3) as int != 1) { return 8; }
    o: Option<long> = Option.fromFlag(true, 42);
    if (o.unwrapOr(0) != 42) { return 9; }
    n: Option<str> = Option.nothing();
    if (n.isSome()) { return 10; }
    r: Result<long, str> = Result.okIf(false, 1, "no");
    match r { Ok(x) { return 11; } Err(e) { if (e.len != 2) { return 12; } } }
    println("ok");
    return 0;
}
