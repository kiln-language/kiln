// `a, b = (b, a)` swaps: the tuple is read whole before either target is written. Locals, fields,
// elements, `inout` parameters and a mix, and a rotation of three.
struct P { x: long, y: long }
swapIn inout a:long inout b:long -> void { a, b = (b, a); }
swapFields inout p:P -> void { p.x, p.y = (p.y, p.x); }
main -> int {
    a: long = 1;
    b: long = 2;
    a, b = (b, a);
    if (a != 2 || b != 1) { return 1; }
    p: P = P { x: 3, y: 4 };
    p.x, p.y = (p.y, p.x);
    if (p.x != 4 || p.y != 3) { return 2; }
    xs: [long; 3] = [5, 6, 7];
    xs[0], xs[2] = (xs[2], xs[0]);
    if (xs[0] != 7 || xs[2] != 5 || xs[1] != 6) { return 3; }
    swapIn(&a, &b);
    if (a != 1 || b != 2) { return 4; }
    swapFields(&p);
    if (p.x != 3 || p.y != 4) { return 5; }
    a, p.x, xs[1] = (p.x, xs[1], a);
    if (a != 3 || p.x != 6 || xs[1] != 1) { return 7; }
    c: long = 9;
    a, b, c = (b, c, a);
    if (a != 2 || b != 9 || c != 3) { return 8; }
    return 0;
}
