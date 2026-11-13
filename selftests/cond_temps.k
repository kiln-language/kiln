// An owning temporary, or a move, inside a condition or a short-circuit operand happens only when
// that operand is reached, in order, and is released on the path that made it: `||` and `&&`,
// the first condition of an `if`, an `else if`'s, and a `while`'s, which runs every time round.
#include <stdlib::io>

var gMade: long = 0;
var gDrops: long = 0;
var gLog: long = 0;            // each call appends a digit: 1 = bump, 2 = snap
struct Snap { n: long }
methods Snap for Drop { drop &self -> void { gDrops = gDrops + 1; } }
methods Snap { len &self -> long { return self.n; } }
struct Ctr { n: long }
methods Ctr {
    bump &self -> long { self.n = self.n + 1; gLog = gLog * 10 + 1; return self.n; }
    snap &self -> Snap { gMade = gMade + 1; gLog = gLog * 10 + 2; return Snap { n: self.n }; }
}

var gTaken: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gTaken = gTaken + 1; } }
take sink r:Res -> long { return r.n; }
yes -> bool { return true; }

main -> int {
    c: Ctr = Ctr { n: 0 };
    // Reached, so built after the left operand ran, and released.
    if (c.bump() != 1 || c.snap().len() != 1) { return 1; }
    if (gLog != 12 || gMade != 1 || gDrops != 1) { return 2; }
    gLog = 0;
    // Short-circuited: never built.
    if (c.bump() == 2 || c.snap().len() == 99) { } else { return 3; }
    if (gLog != 1 || gMade != 1) { return 4; }
    gLog = 0;
    ok: bool = c.bump() == 100 && c.snap().len() == 3;
    if (ok || gLog != 1 || gMade != 1) { return 5; }
    // A chain of three, each operand in turn.
    gLog = 0;
    if (c.bump() == 4 && c.snap().len() == 4 && c.bump() == 5 && c.snap().len() == 5) { } else { return 6; }
    if (gLog != 1212 || gMade != 3 || gDrops != 3) { return 7; }
    // `else if`: built only when that link is reached, and released.
    if (c.n == 5) { } else if (c.snap().len() == 5) { return 8; }
    if (gMade != 3) { return 9; }
    if (c.n == 99) { } else if (c.snap().len() == 5) { } else { return 10; }
    if (gMade != 4 || gDrops != 4) { return 11; }
    // `while`: built and released every time the condition runs (four times: 5, 6, 7, then 8).
    while (c.snap().len() < 8) { c.n = c.n + 1; }
    if (gMade != 8 || gDrops != 8) { return 12; }

    // Moves: recorded on the path that made them, so the owner releases exactly what it kept.
    { r: Res = Res { n: 3 }; if (take(r) != 3) { return 13; } }
    if (gTaken != 1) { return 14; }
    { r: Res = Res { n: 3 }; if (yes() || take(r) > 0) { } }
    if (gTaken != 2) { return 15; }
    { r: Res = Res { n: 3 }; if (!yes() || take(r) > 0) { } }
    if (gTaken != 3) { return 16; }
    { r: Res = Res { n: 4 }; if (gTaken == 99) { } else if (take(r) == 4) { } }
    if (gTaken != 4) { return 17; }
    { r: Res = Res { n: 4 }; if (gTaken == 4) { } else if (take(r) == 4) { return 18; } }
    if (gTaken != 5) { return 19; }
    println("conditions: {} temporaries built, {} released; {} owned values released once each",
            gMade, gDrops, gTaken);
    return 0;
}
