// `methods X for Drop` in a program that includes nothing: the drop runs (it used to name a trait
// no one had declared, and never ran). Exit code: the three releases.
var gDrops: long = 0;
struct R { x: long }
methods R for Drop { drop &self -> void { gDrops = gDrops + 1; } }
take r:R -> long { return r.x; }
main -> int {
    { r: R = R { x: 1 }; take(r); }
    { a: R = R { x: 2 }; b: R = R { x: 3 }; }
    return gDrops as int;
}
