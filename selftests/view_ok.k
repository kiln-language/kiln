// What the no-escape rule for views allows: a view of what a parameter holds, or of its storage,
// handed back; static data kept in a global; a view local read while its source is left alone,
// and the source changed once the view is not read again. Exits 42 when every case held.
#include <stdlib::{io, vec, string}>

struct Tok { text: str, n: long }
struct Bag { items: Vec<long>, count: long }
methods Bag {
    view &self -> [long] { return self.items.asSlice(); }
    bump &self -> void { self.count = self.count + 1; }
}

var gstr: str = "";

trimmed s:str -> str { return strTrim(s); }                                  // part of a parameter
firstTok toks:&Vec<Tok> -> str { t: Tok = toks.get(0); return t.text; }       // what a parameter holds
setStatic -> void { gstr = "static"; }                                        // static data in a global

main -> int {
    code: int = 0;
    if (trimmed("  hi  ") == "hi") { code = code + 1; }
    toks: Vec<Tok>;
    toks.push(Tok { text: "tok", n: 1 });
    if (firstTok(&toks) == "tok") { code = code + 1; }
    setStatic();
    if (gstr == "static") { code = code + 1; }
    // Read while the source is left alone, then the source grown once the view is done.
    v: Vec<long>;
    v.push(5); v.push(6);
    s: [long] = v.asSlice();
    total: long = s[0] + s[1];
    v.push(7);
    if (total == 11 && v.len() == 3) { code = code + 1; }
    // A view of a field of `b`; another field written while it lives.
    items: Vec<long>;
    items.push(1); items.push(2); items.push(3);
    b: Bag = Bag { items: items, count: 0 };
    w: [long] = b.view();
    b.bump();
    if (w[2] == 3 && b.count == 1) { code = code + 1; }
    // A view made fresh each time round, its source grown after its last read in the round.
    buf: Vec<u8>;
    n: long = 0;
    for i in 0..3 {
        buf.push(65 + i as u8);
        t: str = buf.asSlice() as str;
        n = n + t.len;
        buf.push(10);
    }
    if (n == 9) { code = code + 1; }
    // A condition reads the view, and the branch it picks changes the source.
    u: [long] = v.asSlice();
    if (u[0] == 5) { v.push(8); }
    if (v.len() == 4) { code = code + 1; }
    return code + 35;
}
