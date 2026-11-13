// A function that writes an `inout` parameter cannot stand behind a fn type: `f(p)` would write
// `p` with nothing at the call to say so.
struct P { x: long }
bump inout p:P -> void { p.x = p.x + 1; }
main -> int { p: P = P { x: 1 }; f: fn(P)->void = &bump; f(p); return p.x as int; }
