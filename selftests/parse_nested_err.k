#include <stdlib::io>

// An error inside a closure inside a method is one error in the `methods` block that holds it: the
// rest of the block is skipped (the missing `;` in `reset` is not reported), and the declarations
// after it are read. One in a closure nested in another is reported where it is.

struct Counter { n: long }

methods Counter {
    bump &self -> void { self.n = self.n + 1; }
    scaled &self k:long -> long {
        f: Fn(long) -> long = |x: long| { return x * ; };
        return f(self.n);
    }
    reset &self -> void { self.n = 0 }
}

run<F: Fn() -> void> f:F -> void { f(); }

go -> long {
    n: long = 0;
    run(|| { run(|| { n = n + ; }); });
    return n;
}

later -> long { return 7 }

main -> long { c: Counter = Counter { n: 0 }; c.bump(); return go() + later(); }
