// A signed remainder by a power of two: tested against zero it is a mask of the low bits, used as
// a value it keeps its sign. Through fn values, so nothing folds the arguments in.
even x:long -> bool { return x % 2 == 0; }
odd4 x:long -> bool { return x % 4 != 0; }
rem x:long -> long { return x % 4; }
both x:long -> long { r: long = x % 8; if (r == 0) { return 100; } return r; }
narrow x:int -> bool { return x % 16 == 0; }
// Against a value other than zero the sign matters: -3 % 4 is -3, whose low bits are 1.
one x:long -> bool { return x % 4 == 1; }
main -> int {
    e: fn(long) -> bool = &even;
    o: fn(long) -> bool = &odd4;
    r: fn(long) -> long = &rem;
    b: fn(long) -> long = &both;
    n: fn(int) -> bool = &narrow;
    q: fn(long) -> bool = &one;
    if (!e(-6) || e(-7) || !e(0) || e(9)) { return 1; }
    if (o(-8) || !o(-7) || !o(5)) { return 2; }
    if (r(-5) != -1 || r(7) != 3) { return 3; }
    if (b(-16) != 100 || b(-13) != -5 || b(13) != 5) { return 4; }
    if (!n(-32) || n(-33) || !n(2147483632)) { return 5; }
    if (q(-3) || !q(5) || q(-7)) { return 6; }
    return 0;
}
