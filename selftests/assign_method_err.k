struct Counter { n: long }
methods Counter { get &self -> long { return self.n; } }
main -> int {
    c: Counter = Counter { n: 1 };
    c.get() = 3;
    return c.n as int;
}
