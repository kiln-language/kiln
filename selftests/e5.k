struct Point { x: long, y: long }

area p:Point -> long { return p.x * p.y; }

main -> long {
    p: Point;
    p.x = 6;
    p.y = 7;
    n: long = p.x + p.y;
    p.x = n;
    return p.x - 1;
}
