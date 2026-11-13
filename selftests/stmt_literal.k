// A statement may open with a literal or a parenthesis: a method called on a string literal, a
// number, or a parenthesized expression, its value discarded. Exit code: 2 + 3 + 4 + 3 = 12.
var gSeen: long = 0;
methods str { note &self -> long { gSeen = gSeen + self.len; return self.len; } }
trait Bump { bump &self -> long; }
methods int for Bump { bump &self -> long { gSeen = gSeen + (self as long); return self as long; } }
main -> int {
    "ab".note();
    3.bump();
    (2 + 2).bump();
    ("abc").note();
    return gSeen as int;
}
