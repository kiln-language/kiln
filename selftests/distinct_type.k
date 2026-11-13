// `type X = distinct Y`: Y's representation and calling convention, a type of its own. It
// converts only by `as`, has an operator only where it implements the operator's trait, keeps
// its own methods and impls apart from Y's, works as a generic argument and a Vec element, prints
// through its own `Display` (in a macro too), and encodes through the Encode derive as its integer.
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::string>
#include <stdlib::encode>

type Meters = distinct long;
type Feet = distinct long;
type Flag = distinct bool;
type Small = distinct u8;
enum Color: int { Red, Green }
type Paint = distinct Color;

methods Meters {
    toFeet &self -> Feet { return ((self as long) * 328 / 100) as Feet; }
    twice &self -> Meters { return ((self as long) * 2) as Meters; }
}
methods Feet { twice &self -> Feet { return ((self as long) * 20) as Feet; } }   // its own, not Meters'
methods Meters for Add<Meters> { add self o:Meters -> Meters { return ((self as long) + (o as long)) as Meters; } }
methods Meters for Eq<Meters> { eq &self o:Meters -> bool { return (self as long) == (o as long); } }
methods Meters for Ord { cmp &self o:Meters -> long { return (self as long) - (o as long); } }
methods Meters for Display { display &self w:Write -> void { putLong(w, self as long); putStr(w, "m"); } }

total xs:Vec<Meters> -> Meters {
    s: Meters = 0 as Meters;
    for x in xs { s = s + x; }
    return s;
}
biggest<T: Ord> a:T b:T -> T { if (a < b) { return b; } return a; }
shown -> String { return format("[{}]", 42 as Meters); }
macro shownLen -> long { return shown().len; }
asLong m:Meters -> long { return m as long; }      // the same register, the same calling convention

main -> int {
    a: Meters = 5 as Meters;
    b: Meters = 7 as Meters;
    c: Meters = a + b;
    if (!(c == (12 as Meters)) || a == b || !(a < b)) { return 1; }
    v: Vec<Meters>; v.push(a); v.push(b); v.push(c);
    t: Meters = total(v);
    if ((t as long) != 24 || asLong(t) != 24) { return 2; }
    if (!(biggest(a, b) == b)) { return 3; }
    if ((a.toFeet() as long) != 16 || (a.toFeet().twice() as long) != 320 || (a.twice() as long) != 10) { return 4; }
    s: String = format("{} {}", c, t);
    if (s.len != 7) { return 5; }                    // "12m 24m"
    if (shownLen!() != shown().len || shown().len != 5) { return 6; }
    f: Flag = true as Flag;
    if (!(f as bool)) { return 7; }
    sm: Small = 200 as Small;
    if ((sm as long) != 200 || sizeof(Small) != 1 || sizeof(Meters) != 8) { return 8; }
    p: Paint = Color.Green as Paint;
    if ((p as Color) != Color.Green) { return 9; }
    g: Feet = c as Feet;                             // between two distinct types: also `as`
    if ((g as long) != 12) { return 10; }
    bytes: Vec<u8> = encodeValue(t);
    if (bytes.len() != 1) { return 11; }            // its integer: zigzag 24 is one byte
    bv: [u8] = "";
    unsafe { bv = bytesOf(&bytes); }
    r: Result<Meters, str> = decodeValue(bv);
    match r { Ok(back) { if (!(back == t)) { return 12; } } Err(e) { return 13; } }
    return 0;
}
