#include <stdlib::{io, recover}>

// A closure's body is `unsafe` exactly where its text is: inside an `unsafe` block or function it
// may read through a raw pointer or `recover`, and elsewhere it is safe code that still reads and
// writes the scalars it captured.

viaBound<F: Fn() -> void> f:F -> void { f(); }
viaObj f:Fn() -> void -> void { f(); }
twice<F: Fn(long) -> long> f:F x:long -> long { return f(f(x)); }

struct Cell { v: long }
methods Cell {
    // an `unsafe` method's body is trusted, and so is a closure written in it
    unsafe peekVia &self p:*long -> long { r: long = 0; viaObj(|| { r = p[0] + self.v; }); return r; }
}

// captures written and read in safe code
counts -> long {
    n: long = 0;
    k: long = 5;
    viaBound(|| { n = n + k; k = k - 1; });
    viaObj(|| { n = n * 10 + k; });
    return n;               // 5 * 10 + 4
}

// a closure inside an `unsafe` block reads through a raw pointer
fromBlock -> long {
    n: long = 41;
    got: long = 0;
    unsafe {
        q: *long = &n as *long;
        viaBound(|| { got = q[0] + 1; });
    }
    return got;
}

// a closure inside an `unsafe` function, and one nested in it, both trusted
unsafe fromFn p:*long -> long {
    a: long = 0;
    viaObj(|| { a = *p; viaBound(|| { a = a + p[1]; }); });
    recover { viaObj(|| { a = a + 100; raise(); }); } else { a = a + 1000; }
    return a;
}

// a safe closure holding its own `unsafe` block
ownBlock -> long {
    n: long = 9;
    out: long = 0;
    viaObj(|| { unsafe { q: *long = &n as *long; out = q[0]; } });
    return out;
}

// a generic closure in safe code, captured scalars and parameters
scaled<T: Copy> v:T k:long -> long { m: long = 0; viaBound(|| { m = k * 3; }); return m; }

main -> long {
    if (counts() != 54) { return 1; }
    if (fromBlock() != 42) { return 2; }
    arr: [long; 2] = [20, 22];
    r: long = 0;
    unsafe { r = fromFn(&arr[0] as *long); }
    if (r != 1142) { return 3; }
    if (ownBlock() != 9) { return 4; }
    if (twice(|x: long| x * 2, 3) != 12) { return 5; }
    if (scaled(Cell { v: 1 }, 4) != 12) { return 6; }
    c: Cell = Cell { v: 3 };
    s: long = 0;
    unsafe { s = c.peekVia(&arr[1] as *long); }
    if (s != 25) { return 7; }
    println("closure_unsafe_ok");
    return 0;
}
