struct Point { x: long, y: long }
struct Line { a: Point, b: Point }

len l:Line -> long { return l.b.x - l.a.x + l.b.y - l.a.y; }

main -> long {
    p: Point = Point { x: 1, y: 2 };
    q: Point = Point { x: 9, y: 12 };
    l: Line = Line { a: p, b: q };
    return len(l);
}
