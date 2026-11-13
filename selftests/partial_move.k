// Moving one field out of an owned local struct leaves the rest of it owned: the moved field is
// gone, the others stay readable, and the scope's end releases only the owning fields still
// there. Unconditionally moved, nothing at run time records it; moved on some paths only (one
// arm of an `if`, an iteration of a loop the value is declared in), a flag per field does. A
// store gives the field (or the whole value) back. Every release is counted, by value.
#include <stdlib::io>
#include <stdlib::string>

var gDrops: long = 0;
struct Res { id: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.id; } }
struct Acc { s: Res, t: Res, n: long }
mk id:long -> Res { return Res { id: id }; }
mkAcc a:long b:long -> Acc { return Acc { s: mk(a), t: mk(b), n: 7 }; }
eat sink r:Res -> long { return r.id; }

cond c:bool -> long {
    acc: Acc = mkAcc(1, 2);
    if (c) { eat(acc.s); }
    return acc.n;
}
both c:bool -> long {
    acc: Acc = mkAcc(1, 2);
    if (c) { eat(acc.s); } else { eat(acc.t); }
    return acc.n;
}
viaReturn -> Res {
    acc: Acc = mkAcc(10, 20);
    return acc.t;
}
inLoop n:long -> long {
    i: long = 0;
    tot: long = 0;
    while (i < n) {
        acc: Acc = mkAcc(100, 200);
        if (i % 2 == 0) { tot = tot + eat(acc.s); }
        i = i + 1;
    }
    return tot;
}
earlyOut c:bool -> long {
    acc: Acc = mkAcc(1000, 2000);
    if (c) { eat(acc.s); return 1; }
    return acc.s.id;
}
fieldBack -> long {
    acc: Acc = mkAcc(10000, 20000);
    r: Res = acc.s;
    acc.s = mk(30000);
    return r.id + acc.s.id;
}
wholeBack c:bool -> long {
    acc: Acc = mkAcc(100000, 200000);
    if (c) { eat(acc.t); }
    acc = mkAcc(300000, 400000);
    return acc.n;
}
param a:Acc -> long { s: Res = a.s; return s.id + a.n; }
shortCircuit c:bool -> long {
    acc: Acc = mkAcc(1, 2);
    if (c && eat(acc.s) > 0) { return 1; }
    return 0;
}

// The same, run by the compile-time evaluator: the global is folded.
struct SS { s: String, t: String, n: long }
foldPartial k:long -> long {
    a: SS = SS { s: stringOf("abc"), t: stringOf("de"), n: 1 };
    got: long = 0;
    if (k > 0) { x: String = a.s; got = x.len; }
    return got + a.t.len + a.n;
}
gFold: long = foldPartial(1);

main -> int {
    {
        acc: Acc = mkAcc(1, 2);
        s: Res = acc.s;
        if (s.id != 1 || acc.t.id != 2 || acc.n != 7) { return 1; }
    }
    if (gDrops != 3) { return 2; }
    gDrops = 0; cond(true);  if (gDrops != 3) { return 3; }
    gDrops = 0; cond(false); if (gDrops != 3) { return 4; }
    gDrops = 0; both(true);  if (gDrops != 3) { return 5; }
    gDrops = 0; both(false); if (gDrops != 3) { return 6; }
    gDrops = 0; { x: Res = viaReturn(); if (gDrops != 10) { return 7; } } if (gDrops != 30) { return 8; }
    gDrops = 0; inLoop(3); if (gDrops != 900) { return 9; }
    gDrops = 0; earlyOut(true);  if (gDrops != 3000) { return 10; }
    gDrops = 0; earlyOut(false); if (gDrops != 3000) { return 11; }
    gDrops = 0; if (fieldBack() != 40000 || gDrops != 60000) { return 12; }
    gDrops = 0; wholeBack(true);  if (gDrops != 1000000) { return 13; }
    gDrops = 0; wholeBack(false); if (gDrops != 1000000) { return 14; }
    gDrops = 0; if (param(mkAcc(5, 6)) != 12 || gDrops != 11) { return 15; }
    gDrops = 0; shortCircuit(true);  if (gDrops != 3) { return 16; }
    gDrops = 0; shortCircuit(false); if (gDrops != 3) { return 17; }
    if (gFold != 6 || foldPartial(0) != 3) { return 18; }
    println("ok");
    return 0;
}
