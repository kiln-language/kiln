// A variant of a generic enum built without naming its instance takes its type from where it
// goes: a parameter (a method's or a function's), a return, an assignment, a field.
#include <stdlib::io>
#include <stdlib::option>
#include <stdlib::result>
struct Conn { t: long }
methods Conn { setT &self t:Option<long> -> void { match t { Some(v) { self.t = v; } None { self.t = -1; } } } }
take t:Option<long> -> long { match t { Some(v) { return v; } None { return -1; } } }
both t:Option<long> r:Result<long, str> -> long {
    n: long = take(t);
    match r { Ok(v) { return n + v; } Err(e) { return n - e.len; } }
}
give -> Option<long> { return Option.Some(250000000); }
struct H { o: Option<long> }
main -> int {
    c: Conn = Conn { t: 0 };
    c.setT(Option.Some(250000000));
    if (c.t != 250000000) { return 1; }
    c.setT(Option.None);
    if (c.t != -1) { return 2; }
    if (take(Option.Some(5)) != 5 || take(give()) != 250000000) { return 3; }
    o: Option<long> = Option.None;
    o = Option.Some(7);
    h: H = H { o: Option.Some(8) };
    if (take(o) + take(h.o) != 15) { return 4; }
    if (both(Option.Some(1), Result.Ok(2)) != 3 || both(Option.None, Result.Err("abc")) != -4) { return 5; }
    return 0;
}
