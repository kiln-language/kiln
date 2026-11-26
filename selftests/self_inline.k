#include <stdlib::recover>
// A function's call to itself replaced by copies of its own body, two levels deep
// (`Relayout.selfInline`), the accumulator a copy adds into merged with its caller's
// (`--no-merge-acc`). Each answer below is what the program printed built without either.
//
// `fib`: the accumulator form, merged. `visit`: writes a global on the way in, so the order of
// the copies' side effects shows in the hash. `poly`: the result used in more than an addition,
// so the copies keep their own results. `deep`: a hundred thousand levels, each frame now
// standing for three. `holder` keeps a `Drop` value, `guarded` a `recover`, and `ping`/`pong`
// call each other: each of those stays a call, and gives the same answer.

var gTrace: long = 0;
var gDrops: long = 0;

fib n:long -> long {
    if (n < 2) { return n; }
    return fib(n - 1) + fib(n - 2);
}

visit n:long -> long {
    gTrace = gTrace * 31 + n;
    if (n < 2) { return n; }
    return visit(n - 1) + visit(n - 2);
}

poly n:long -> long {
    if (n < 1) { return 1; }
    return (poly(n - 1) * 3 + n) % 1000003;
}

deep n:long -> long {
    if (n == 0) { return 1; }
    return (deep(n - 1) * 7 + 3) % 1000003;
}

// The copy writes its parameter, so it needs a temp of its own: the argument `k` is read again
// after the call.
countdown n:long -> long {
    if (n < 1) { return 0; }
    k: long = n - 1;
    s: long = countdown(k) + k;
    n = n * 2 + s % 7;
    return s + n;
}

struct Tick { v: long }
methods Tick for Drop { drop &self -> void { gDrops = gDrops + self.v; } }

holder n:long -> long {
    t: Tick = Tick { v: n };
    if (n < 2) { return n; }
    return holder(n - 1) + holder(n - 2) + t.v;
}

guarded n:long -> long {
    r: long = 0;
    unsafe {
        recover {
            if (n < 2) { r = n; } else { r = guarded(n - 1) + guarded(n - 2); }
        } else {
            r = 0 - 1;
        }
    }
    return r;
}

ping n:long -> long {
    if (n <= 0) { return 1; }
    return pong(n - 1) + 1;
}
pong n:long -> long {
    if (n <= 0) { return 2; }
    return ping(n - 1) * 2;
}

main -> int {
    if (fib(30) != 832040) { return 1; }
    v: long = visit(16);
    if (v != 987) { return 2; }
    if (gTrace != 6498559210187465686) { return 3; }
    if (poly(25) != 618262) { return 4; }
    if (deep(100000) != 940193) { return 5; }
    if (holder(12) != 972) { return 6; }
    if (gDrops != 972) { return 7; }
    if (guarded(15) != 610) { return 8; }
    if (ping(21) != 4095) { return 9; }
    if (countdown(30) != 1455) { return 10; }
    return 0;
}
