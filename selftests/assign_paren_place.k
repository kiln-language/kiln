// A place in parentheses is still that place: a local, a field, an element, through a pointer.
struct P { x: long, y: long }
main -> int {
    a: long = 0;
    (a) = 5;
    p: P = P { x: 0, y: 0 };
    (p.x) = 7;
    xs: [long; 3] = [0, 0, 0];
    (xs[1]) = 9;
    q: *long;
    unsafe { q = &a; }
    unsafe { (*q) = 11; }
    ((p.y)) = 13;
    (a) += 1;
    if (a != 12 || p.x != 7 || xs[1] != 9 || p.y != 13) { return 1; }
    return 0;
}
