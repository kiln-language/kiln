// A store through a pointer ends what is known of the bytes it writes and of what other pointers
// may reach, but not of the bytes beside it under the same pointer: the field read before a store
// to another field of the same struct is not read again, through a borrowed parameter and through a
// raw pointer alike (`killRegion`, which finds the pointer's other locations by its root).
// ir-count: store_beside::viaBorrow ptrload 1
// ir-count: store_beside::viaRaw ptrload 1
struct P { a: long, b: long }

viaBorrow inout r:P -> long {
    x: long = r.b;
    r.a = x + 1;
    return x + r.b;
}
viaRaw p:*P -> long {
    x: long = 0;
    unsafe {
        x = p.b;
        p.a = x + 1;
        x = x + p.b;
    }
    return x;
}

main -> long {
    q: P = P { a: 1, b: 2 };
    s: long = viaBorrow(&q) + viaBorrow(&q);
    t: long = 0;
    unsafe { t = viaRaw(&q as *P); }
    if (s != 8 || q.a != 3 || t != 4) { return 1; }
    return 0;
}
