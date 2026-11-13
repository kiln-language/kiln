// `format` (and every `...any` function) runs inside a macro: the evaluator boxes each argument
// as the lowerer does, a `Display` value through its own `display`. What a macro builds is
// checked against the same call made at runtime, byte for byte (a checksum, since a macro hands
// back a number), and once more where a struct's `Display` itself formats.
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::string>

struct P { x: long, y: long }
methods P for Display { display &self w:Write -> void { putStr(w, "P("); putLong(w, self.x); putStr(w, ", "); putLong(w, self.y); putStr(w, ")"); } }
struct Q { p: P, tag: str }
methods Q for Display { display &self w:Write -> void { s: String = format("<{} {}>", self.tag, self.p); unsafe { putStr(w, s.view()); } } }

sumOf s:String -> long {
    h: long = 0;
    i: long = 0;
    v: str = "";
    unsafe { v = s.view(); }
    while (i < v.len) { h = h * 31 + (charAt(v, i) as long) + 1; h = h % 1000000007; i = i + 1; }
    return h * 100 + v.len;
}
built -> String {
    p: P = P { x: 3, y: -4 };
    q: Q = Q { p: P { x: 1, y: 2 }, tag: "q" };
    d: Display = p;
    return format("{}.{} is {} / {} / {} / {:>5} / {:x} / [{}] / {} / {}", "T", "f", 42, 'c', 5000000000, 7, 255, p, q, d);
}
macro atCompile -> long { return sumOf(built()); }

main -> int {
    if (atCompile!() != sumOf(built())) { return 1; }
    s: String = built();
    if (s.len < 40) { return 2; }
    return 0;
}
