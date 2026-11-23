// Arguments that trade places: each lives in another one's register when the call is made, and
// the moves that put them in place must not overwrite one still to be read.
sub3 a:long b:long c:long -> long { return a * 100 + b * 10 + c; }
rot a:long b:long c:long -> long {
    f: fn(long, long, long) -> long = &sub3;
    x: long = f(c, a, b);
    y: long = f(b, c, a);
    z: long = f(b, a, c);
    return x * 1000000 + y * 1000 + z;
}
main -> int {
    g: fn(long, long, long) -> long = &rot;
    if (g(1, 2, 3) != 312231213) { return 1; }
    return 0;
}
