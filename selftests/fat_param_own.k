// A `str`, slice or trait-object parameter taken by value is the callee's own: writing it, or
// lending it to something that writes it, must not change the caller's value. The callee reached
// the pair through the caller's address and used to write straight into it.
trait Shape { area &self -> long; }
struct Sq { s: long }
methods Sq for Shape { area &self -> long { return self.s * self.s; } }

var gText: str = "global";

reslice xs:[long] -> long { xs = xs[1..]; return xs.len; }
cut s:str -> long { s = s[2..]; return s.len; }
shorten s:str -> long { unsafe { s.len = 1; } return s.len; }
viaPtr s:str -> long { unsafe { p: *str = &s; *p = "zz"; } return s.len; }
swap s:str t:str -> long { s, t = (t, s); return s.len * 10 + t.len; }
regrow inout xs:[long] -> void { xs = xs[1..]; }
lendOn xs:[long] -> long { regrow(&xs); return xs.len; }
other sh:Shape alt:Shape -> long { sh = alt; return sh.area(); }
readOnly s:str -> long { return s.len; }

main -> int {
    a: [long; 3] = [1, 2, 3];
    v: [long] = a[..];
    if (reslice(v) != 2 || v.len != 3) { return 1; }
    t: str = "hello";
    if (cut(t) != 3 || t.len != 5) { return 2; }
    if (cut(gText) != 4 || gText.len != 6) { return 3; }
    if (shorten(t) != 1 || t.len != 5) { return 4; }
    if (viaPtr(t) != 2 || t.len != 5) { return 5; }
    u: str = "x";
    if (swap(t, u) != 15 || t.len != 5 || u.len != 1) { return 6; }
    w: [long] = a[..];
    regrow(&w);
    if (w.len != 2) { return 7; }
    // Lent on to something that shortens it: the caller's slice stays as it was.
    if (lendOn(v) != 2 || v.len != 3) { return 13; }
    p: Sq = Sq { s: 3 };
    q: Sq = Sq { s: 4 };
    if (other(p, q) != 16 || p.area() != 9) { return 8; }
    // The same bodies through fn values, which no inlining reaches.
    fc: fn(str) -> long = &cut;
    if (fc(t) != 3 || t.len != 5) { return 9; }
    fr: fn([long]) -> long = &reslice;
    if (fr(v) != 2 || v.len != 3) { return 10; }
    fs: fn(str) -> long = &shorten;
    if (fs(t) != 1 || t.len != 5) { return 11; }
    if (readOnly(t) != 5) { return 12; }
    return 0;
}
