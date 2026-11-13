// A flow miscompile: the optimizer keyed a hidden scratch slot's memory as 2^40 + its number, and
// 2^40 was written `1 << 40`, which was computed as an `int` and came out 0 -- so scratch slot
// #137 and the local whose name is symbol 137 were one place to it, and `v.id` below was "known"
// to hold the 1 a scratch slot was given for `Res { id: 1 }`. Which numbers meet depends on the
// whole program; this is the program it was found in (tests/stdlib-option/option_own.k), with
// the payloads it must keep summed (1 + 2 + 4 = 7) and every release counted (1 + 3 + 2 + 4): 80.
#include <stdlib::option>
struct Res { id: long }
var gReleased: long = 0;
methods Res for Drop { drop &self -> void { gReleased = gReleased + self.id; } }
idOf r:Res -> long { return r.id; }
main -> int {
    a: Option<Res> = Option.Some(Res { id: 1 });
    m: Option<long> = mapOption(a, &idOf);
    t: long = 0;
    match m { Some(v) { t = t + v; } None { t = t + 100; } }
    e: Option<Res>;
    m2: Option<long> = mapOption(e, &idOf);
    match m2 { Some(v) { t = t + 100; } None { } }
    b: Option<Res> = Option.Some(Res { id: 2 });
    c: Option<Res> = Option.Some(Res { id: 3 });
    d: Option<Res> = orOption(b, c);
    match d { Some(v) { t = t + v.id; } None { t = t + 100; } }
    f: Option<Res>;
    g: Option<Res> = Option.Some(Res { id: 4 });
    h: Option<Res> = orOption(f, g);
    match h { Some(v) { t = t + v.id; } None { t = t + 100; } }
    return (t * 10 + gReleased) as int;
}
