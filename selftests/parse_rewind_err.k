#include <stdlib::io>

// Declarations that register things before their error is found, taken back whole: a closure (its
// capture struct, its mark, its `Fn` implementation), an instance of a generic struct nothing else
// had asked for, and a macro's name. The instance asked for again below is asked for anew, and the
// gate's `rewind` line holds the registry to the operations that survive.

struct Pair<A, B> { a: A, b: B }

f x:long -> long {
    g: Fn(long) -> long = |y: long| y + x;
    p: Pair<long, bool> = Pair { a: g(1), b: true };
    return p.a + ;
}

h -> long {
    p: Pair<long, bool> = Pair { a: 2, b: false };
    return p.a;
}

main -> long { return h(); }

macro broken e:long -> long { return e;
