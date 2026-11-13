// `a, b = t;` takes a tuple apart. From an owned tuple each name takes its element (a move per
// element, so each is released once, by the name that has it, and nothing is left for the tuple);
// from a borrowed one (a match through a borrow, a field of `&self`, an `inout` parameter) each
// owning element is bound as a borrow of the element where it lies, and nothing is moved or
// released. Every release is counted.
#include <stdlib::io>
#include <stdlib::result>
#include <stdlib::option>
#include <stdlib::string>

var gDrops: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.n; } }
mk n:long -> Res { return Res { n: n }; }

open n:long -> (Res, String) { s: String = stringOf("r"); s.pushLong(n); return (mk(n), s); }
two -> (Res, Res) { return (mk(100), mk(1000)); }
accept n:long -> Result<(Res, long), long> {
    if (n < 0) { return Result.Err(n); }
    return Result.Ok((mk(n), n + 1));
}

struct Holder { p: (Res, long), r: Result<(Res, String), long> }
methods Holder {
    peek &self -> long { a, b = self.p; return a.n + b; }
    peekR &self -> long {
        match self.r {
            Ok(t) { q, w = t; return q.n + w.len; }
            Err(e) { return e; }
        }
    }
    bump &self -> void { a, b = self.p; a.n = a.n + 1; }          // writes through the borrow
}
look inout r:Result<(Res, String), long> -> long {
    match r { Ok(t) { q, w = t; return q.n + w.len; } Err(e) { return e; } }
}
// The names may be moved on: each owns its element.
handOn -> Res { r, s = open(7); return r; }

main -> int {
    {
        r, s = open(1);
        if (r.n != 1 || s.len != 2) { return 1; }
    }
    if (gDrops != 1) { return 2; }
    {
        x, y = two();
        if (x.n + y.n != 1100) { return 3; }
    }
    if (gDrops != 1101) { return 4; }
    gDrops = 0;

    // Out of a Result's arm, owned: the arm's binding is taken apart.
    {
        res: Result<(Res, long), long> = accept(5);
        match res {
            Ok(t) { a, b = t; if (a.n != 5 || b != 6) { return 5; } }
            Err(e) { return 6; }
        }
        bad: Result<(Res, long), long> = accept(-2);
        match bad { Ok(t) { return 7; } Err(e) { if (e != -2) { return 8; } } }
    }
    if (gDrops != 5) { return 9; }
    gDrops = 0;

    // Through borrows: nothing moved, nothing released until the holder goes.
    {
        h: Holder = Holder { p: (mk(10), 2), r: Result.Ok((mk(20), stringOf("abc"))) };
        if (h.peek() != 12 || h.peekR() != 23) { return 10; }
        h.bump();
        if (h.p.0.n != 11) { return 11; }
        if (look(&h.r) != 23) { return 12; }
        if (gDrops != 0) { return 13; }
    }
    if (gDrops != 31) { return 14; }
    gDrops = 0;

    {
        k: Res = handOn();
        if (k.n != 7) { return 15; }
    }
    if (gDrops != 7) { return 16; }
    println("ok");
    return 0;
}
