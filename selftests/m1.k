struct Counter { seen: long, step: long }

methods Counter {
    bump &self by:long -> long {
        self.seen = self.seen + by * self.step;
        return self.seen;
    }
    total &self -> long { return self.seen; }
}

main -> long {
    c: Counter = Counter { seen: 0, step: 3 };
    c.bump(2);
    c.bump(4);
    return c.total();
}
