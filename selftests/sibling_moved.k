// A value moved in one scope says nothing about a later variable of the same name in another
// scope, of another type: moved in a block, a loop, an `if`, a block that leaves early and a
// match arm, then declared again (with and without a value) in a loop body. Every release counted.
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::option>
#include <stdlib::string>

var gDrops: long = 0;
struct Expr { n: long }
methods Expr for Drop { drop &self -> void { gDrops = gDrops + 1; } }
struct Value { n: long }
methods Value for Drop { drop &self -> void { gDrops = gDrops + 100; } }
mk n:long -> Expr { return Expr { n: n }; }
take e:Expr -> long { return e.n; }

afterBlock -> long {
    n: long = 0;
    { e: Expr = mk(3); n = take(e); }
    for i in 0..2 { e: Vec<Value>; e.push(Value { n: i }); n = n + e.len(); }
    return n;                                            // 3 + 1 + 1
}
afterLoop -> long {
    n: long = 0;
    for i in 0..1 { e: Expr = mk(4); n = take(e); }
    for i in 0..2 { e: Vec<Value> = vec![]; e.push(Value { n: i }); n = n + e.len(); }
    return n;                                            // 4 + 2
}
afterIf x:long -> long {
    n: long = 0;
    if (x > 0) { e: Expr = mk(5); if (x > 1) { n = take(e); } }
    while (n < 9) { e: Vec<Value>; e.push(Value { n: n }); n = n + e.len() + 1; }
    return n;
}
afterContinue -> long {
    n: long = 0;
    for i in 0..3 {
        if (i == 0) { e: Expr = mk(6); n = n + take(e); continue; }
        e: Vec<Value> = vec![];
        e.push(Value { n: i });
        n = n + e.len();
    }
    return n;                                            // 6 + 1 + 1
}
afterMatch o:Option<long> -> long {
    n: long = 0;
    match o { Some(x) { e: Expr = mk(x); n = take(e); } None { } }
    for i in 0..2 { e: Vec<Value>; e.push(Value { n: i }); n = n + e.len(); }
    return n;
}

main -> int {
    if (afterBlock() != 5) { return 1; }
    if (gDrops != 201) { return 2; }                     // one Expr, two Values
    if (afterLoop() != 6) { return 3; }
    if (gDrops != 402) { return 4; }
    if (afterIf(2) != 9) { return 5; }                   // 5, then 7, then 9
    if (gDrops != 603) { return 6; }
    if (afterIf(1) != 10) { return 7; }                  // not moved: released at its block's end
    if (gDrops != 1104) { return 8; }                    // 0, 2, 4, 6, 8: five Values
    if (afterContinue() != 8) { return 9; }
    if (gDrops != 1305) { return 10; }
    if (afterMatch(Option.Some(7)) != 9) { return 11; }
    if (gDrops != 1506) { return 12; }
    if (afterMatch(Option.None) != 2) { return 13; }
    if (gDrops != 1706) { return 14; }
    return 0;
}
