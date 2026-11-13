struct Point { x: long, y: long }

make a:long b:long -> Point {
    p: Point;
    p.x = a;
    p.y = b;
    return p;
}

sum p:Point -> long { return p.x + p.y; }

main -> long {
    q: Point = make(20, 13);
    r: Point = make(1, 2);
    return sum(q) - sum(r);
}
