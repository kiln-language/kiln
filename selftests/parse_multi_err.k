#include <stdlib::{io, vec}>

// Declarations of every kind with an error in each: each error is reported once, and nothing
// else is. The declarations between them are well formed and stay so.

struct Point { x: long, y: long }

struct Broken { a: long, b: }

enum Color { Red, Green, 3 }

trait Shape { area &self -> long; perimeter &self -> ; }

LIMIT: long = 4 * ;

type Pair = (long, long;

sum xs:[long] -> long {
    s: long = 0;
    for x in xs { s = s + x; }
    return s;
}

scale p:Point k:long -> Point { return Point { x: p.x * , y: p.y * k }; }

methods Point { len2 &self -> long { return self.x * self.x + self.y * self.y } }

struct Wrap<T { v: T }

first<T: Copy> xs:[T] -> T { return xs[0] }

main -> long {
    p: Point = Point { x: 3, y: 4 };
    v: Vec<long> = vec![p.x, p.y];
    return sum(v[..]);
}
