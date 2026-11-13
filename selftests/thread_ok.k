// Jump threading (`flow.k`) must send every edge where its own values lead. Flags set on some
// paths and tested after a merge, a flag overwritten by a non-constant after its constant, a
// state machine on an integer, a branch repeating its predecessor's test, a fallthrough edge whose
// constant goes to the taken side, and loops whose exit carries the flag. Each case checked both
// ways.
#include <stdlib::vec>

flagOf x:long -> long {
    found: bool = false;
    if (x > 3) { found = true; }
    if (found) { return 1; }
    return 2;
}

// The last definition on the edge is not the constant.
overwritten x:long -> long {
    ok: bool = true;
    if (x > 3) { ok = x > 10; }
    if (ok) { return 1; }
    return 2;
}

search v:Vec<long> want:long -> long {
    found: bool = false;
    at: long = -1;
    for i in 0..v.len() {
        if (v.get(i) == want) { found = true; at = i; break; }
    }
    if (!found) { return 100; }
    return at;
}

// A small state machine: each arm sets the next state, and the dispatch threads.
machine steps:long -> long {
    state: long = 0;
    acc: long = 0;
    n: long = 0;
    while (n < steps) {
        if (state == 0) { acc = acc + 1; state = 2; }
        else if (state == 1) { acc = acc * 3; state = 0; }
        else { acc = acc + 10; state = 1; }
        n = n + 1;
    }
    return acc;
}

// The same comparison twice: the second is decided by the edge of the first, on each side.
twice x:long -> long {
    r: long = 0;
    if (x < 5) { r = r + 1; }
    if (x < 5) { r = r + 10; } else { r = r + 100; }
    return r;
}

// Constants of a wider kind than a bool, and an unsigned order.
pick k:u8 -> long {
    c: u8 = 200;
    if (k > 3) { c = 7; }
    if (c > 100) { return 1; }
    return 2;
}

// Short-circuit conditions leave a bool on several edges.
both a:long b:long -> long {
    t: bool = a > 0 && b > 0;
    if (t) { return 1; }
    e: bool = a > 0 || b > 0;
    if (e) { return 2; }
    return 3;
}

main -> int {
    if (flagOf(5) != 1 || flagOf(1) != 2) { return 1; }
    if (overwritten(1) != 1 || overwritten(5) != 2 || overwritten(11) != 1) { return 2; }
    v: Vec<long> = vec![4, 8, 15, 16, 23, 42];
    if (search(v, 15) != 2 || search(v, 5) != 100 || search(v, 42) != 5) { return 3; }
    if (machine(0) != 0 || machine(1) != 1 || machine(2) != 11 || machine(3) != 33 || machine(4) != 34) { return 4; }
    if (twice(1) != 11 || twice(9) != 100) { return 5; }
    if (pick(1) != 1 || pick(9) != 2) { return 6; }
    if (both(1, 1) != 1 || both(1, 0) != 2 || both(0, 1) != 2 || both(0, 0) != 3) { return 7; }
    return 42;
}
