// `!b` on a `bool` (or on a comparison) is a `bool`; on an integer it is still "is zero", an `int`.
trait Tag { tag &self -> long; }
methods bool for Tag { tag &self -> long { return 1; } }
methods int  for Tag { tag &self -> long { return 10; } }
flip b:bool -> bool { return !b; }
main -> int {
    t: bool = true;
    n: long = 0;
    a: long = (!t).tag();              // 1: a bool
    b: long = (!(n < 3)).tag();        // 1: a comparison is a truth value
    c: long = (!n).tag();              // 10: an int, 0/1
    d: bool = flip(flip(false));       // false
    e: int = !n;                       // 1
    if (d) { return 99; }
    return (a + b + c + e) as int;     // 13
}
