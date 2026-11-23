// A function called from one place is copied there whatever its size (within a bound), so the
// call is gone and what it computes folds into its caller.
// ir-lacks: main inline_one::big
struct B { x: long, y: long, z: long, w: long }
big i:long -> B {
    a: long = i * 3 + 1;
    b: long = a ^ (a >> 7);
    c: long = b + i;
    d: long = c ^ (c >> 3);
    e: long = d + a;
    f: long = e ^ (e >> 5);
    g: long = f + b;
    h: long = g ^ (g >> 9);
    return B { x: a + h, y: b % 5 + c, z: d % 7 + e, w: f % 3 + g };
}
main -> int {
    t: long = 0;
    for i in 0..1000 { r: B = big(i); t = t + r.x + r.y + r.z + r.w; }
    if (t == 0) { return 1; }
    return 0;
}
