// `match self.field` in a generic type's own methods (it was "'self' has no field 'mode'": the
// parser looked the field up as a struct's only), on an instance's field, and a field whose type
// is an instance over the type parameter. 7 + 9 + 4 + 5 = 25.
#include <stdlib::option>
enum Mode { A, B(long) }
struct Box2<T> { v: T, mode: Mode, opt: Option<T> }
methods Box2<T> {
    tag &self -> long { match self.mode { A { return 0; } B(n) { return n; } } }
    has &self -> long { match &self.opt { Some(x) { return 4; } None { return 0; } } }
}
struct Plain { mode: Mode }
methods Plain { tag &self -> long { match self.mode { A { return 0; } B(n) { return n; } } } }
main -> int {
    p: Plain = Plain { mode: Mode.B(7) };
    g: Box2<long> = Box2 { v: 1, mode: Mode.B(9), opt: Option.Some(3) };
    h: Box2<long> = Box2 { v: 2, mode: Mode.B(5), opt: Option.None };
    r: long = 0;
    match h.mode { A { r = 100; } B(n) { r = n; } }
    return (p.tag() + g.tag() + g.has() + h.has() + r) as int;
}
