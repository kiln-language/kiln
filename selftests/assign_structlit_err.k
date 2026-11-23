struct P { x: long }
main -> int {
    p: P = P { x: 1 };
    P { x: 2 } = p;
    return p.x as int;
}
