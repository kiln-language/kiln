// The same through a function that hands its parameter on to the one that walks it, and with the
// global reached through a field. Refused (batch 9).
#include <stdlib::{io, vec}>
struct Bag { items: Vec<long>, n: long }
var gBag: Bag = Bag { items: vec![], n: 0 };
grow -> void { gBag.items.push(7); }
walk xs:&Vec<long> -> long { t: long = 0; for x in xs { grow(); t = t + x; } return t; }
outer b:&Bag -> long { return walk(b.items) + b.n; }
main -> int { gBag.items.push(1); return outer(gBag) as int; }
