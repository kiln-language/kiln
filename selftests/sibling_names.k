// A name a sibling scope declared again is a variable of its own. The parser gives sibling
// declarations of one spelling one name (it renames only to shadow), so every pass that keys a
// local by its name has to take each declaration as it comes. A `for x in v` element, a match
// binding through a borrow and a borrowed destructure are borrows; the same name declared as a
// value after (or before) them is a value: writing it writes nothing else, and an owning one is
// released, once. Every release is counted; the same code runs folded.
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::string>

var gDrops: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + 1; } }
mk n:long -> Res { return Res { n: n }; }

struct P { x: long, y: long }
enum E { Full(Res), Empty }

// A for-each over plain structs, then a value of the same name: the value is a copy.
plain -> long {
    v: Vec<P>;
    v.push(P { x: 1, y: 2 });
    v.push(P { x: 3, y: 4 });
    s: long = 0;
    { p: P = v.get(0); p.y = 50; s = s + p.y; }          // a value before the loop
    for p in v { s = s + p.x; }
    { p: P = v.get(1); p.y = p.y + 100; s = s + p.y; }   // and one after it
    for p in v { s = s + p.y * 1000; }                   // the vector is as it was: 2 and 4
    return s;                                            // 50 + 4 + 104 + 6000
}

// The same over owning elements: the loop releases nothing, the value is released once.
owning -> long {
    v: Vec<Res>;
    v.push(mk(1));
    v.push(mk(2));
    t: long = 0;
    for r in v { t = t + r.n; }
    { r: Res = mk(10); r.n = r.n + 1; t = t + r.n; }
    for r in v { t = t + r.n * 100; }
    return t;                                            // 3 + 11 + 300
}

// A match binding through a borrow, then a value of the same name.
viaMatch inout e:E -> long {
    k: long = 0;
    match e { Full(r) { r.n = r.n + 1; k = r.n; } _ { } }
    { r: Res = mk(70); r.n = r.n + 1; k = k + r.n; }
    match e { Full(r) { k = k + r.n * 1000; } _ { } }
    return k;
}

// A borrowed destructure between two values of the same name, the first moved on.
keep r:Res -> long { return r.n; }
struct Holder { p: (Res, long) }
methods Holder {
    viaTuple &self -> long {
        k: long = 0;
        { a: Res = mk(30); a.n = a.n + 1; k = keep(a); }
        { a, b = self.p; k = k + a.n * 100 + b; }
        { a: Res = mk(50); a.n = a.n + 1; k = k + a.n * 10000; }
        return k;
    }
}

// A name declared without a value after a sibling's was declared or assigned with one.
initAgain -> long {
    seen: Vec<str>;
    seen.push("a");
    for s in seen { if (s == "b") { return -1; } }
    s: String;
    s.pushStr("xy");
    return s.len;
}

folded -> long { return plain(); }
FOLDED: long = folded();

main -> int {
    if (plain() != 6158) { return 1; }
    if (gDrops != 0) { return 2; }
    if (owning() != 314) { return 3; }
    if (gDrops != 3) { return 4; }                       // the value, then the two elements
    {
        e: E = E.Full(mk(5));
        if (viaMatch(&e) != 6077) { return 5; }        // 6 + 71 + 6000
        if (gDrops != 4) { return 6; }                   // the value only
        match e { Full(r) { if (r.n != 6) { return 7; } } _ { return 8; } }
    }
    if (gDrops != 5) { return 9; }
    {
        h: Holder = Holder { p: (mk(3), 4) };
        if (h.viaTuple() != 510335) { return 10; }       // 31 + 300 + 4 + 510000
        if (gDrops != 7) { return 11; }                  // the two values, each once
    }
    if (gDrops != 8) { return 12; }
    if (initAgain() != 2) { return 13; }
    if (FOLDED != 6158) { return 14; }
    return 0;
}
