// Two `pub` traits that share a method name, both implemented for one type (they used to clash as
// `P_text` defined twice). The second implementation's methods carry its trait in their symbols;
// `Show.text(p)` names which, a trait object and a bound each reach their own trait's, a method
// only one trait has is called plainly, and a scalar and a generic type do the same. A
// third, `Later`, carries its name too.
// 2 + 200 + 205 + 21 + 202 + 3 + (7 + 700 + 701) + 9 = 2050, returned as 50.
#include <stdlib::vec>
pub trait Show { text &self -> long; }
pub trait Debug2 { text &self -> long; size &self -> long; }
struct P { v: long }
methods P for Show { text &self -> long { return self.v; } }
methods P for Debug2 { text &self -> long { return self.v * 100; } size &self -> long { return 3; } }
methods long for Show { text &self -> long { return self + 1; } }
methods long for Debug2 { text &self -> long { return self + 2; } size &self -> long { return 8; } }
struct Bag<T> { item: T, n: long }
methods Bag<T> for Show { text &self -> long { return self.n; } }
methods Bag<T> for Debug2 { text &self -> long { return self.n * 100; } size &self -> long { return 1; } }
pub trait Later { text &self -> long; }
methods P for Later { text &self -> long { return 9; } }
viaShow<T: Show> x:T -> long { return x.text(); }
viaDebug<T: Debug2> x:T -> long { return x.text() + x.size(); }
objShow s:Show -> long { return s.text(); }
objDebug d:Debug2 -> long { return d.text(); }
main -> int {
    p: P = P { v: 2 };
    a: long = Show.text(p);
    b: long = Debug2.text(p);
    c: long = viaShow(p) + viaDebug(p);
    d: long = viaShow(5 as long) + viaDebug(5 as long);
    e: long = objShow(p) + objDebug(p);
    f: long = p.size();
    g: Bag<long> = Bag { item: 1, n: 7 };
    h: long = Show.text(g) + Debug2.text(g) + viaDebug(g);
    l: long = Later.text(p);
    return (a + b + c + d + e + f + h + l - 2000) as int;
}
