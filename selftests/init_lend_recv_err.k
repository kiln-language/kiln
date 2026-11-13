// A `&self` method on a field of a local declared without a value reads that field.
struct C { n: long }
methods C { bump &self -> void { self.n = self.n + 1; } }
struct W { c: C, k: long }
main -> int {
    w: W;
    w.c.bump();
    return w.c.n as int;
}
