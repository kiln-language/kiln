// `vec![ ... ]`: the raw form of a macro call. The compiler hands `vec` the text between the
// brackets as a `str`; the macro splits it on its top-level commas and reads each piece back as
// code with `parseExpr`, in the module it was called from -- so a struct literal of a type
// declared here resolves. The element type comes from where the result is stored (`v`, `e`,
// the field, the return), or is named up front. Exit code: 15 + 4 = 19.
#include <stdlib::io>
#include <stdlib::vec>

struct P { x: long, y: long }
struct Bag { items: Vec<long>, tags: Vec<str> }

fresh -> Vec<P> { return vec![]; }

main -> int {
    v: Vec<long> = vec![1, 2, 3 * 4];
    w: Vec<str> = vec!["a, b", "c]d"];
    n: long = 5;
    u: Vec<int> = vec![n as int + 1, (2 + 3) * 2];
    ps: Vec<P> = vec![P { x: 1, y: 2 }, P { x: 3, y: 4 }];
    e: Vec<P> = vec![];
    b: Bag = Bag { items: vec![7, 8], tags: vec![] };
    f: Vec<P> = fresh();
    t: Vec<u8> = vec![u8: 250, 5];
    sum: long = 0;
    i: long = 0;
    while (i < v.len()) { sum = sum + v.get(i); i = i + 1; }
    println("{} {} {} {} {} {} {} {} {} {} {}", sum, w.get(0), w.get(1), u.get(0), u.get(1), ps.get(1).x,
            e.len(), b.items.get(1), b.tags.len(), f.len(), (t.get(0) + t.get(1)) as long);
    return (sum + ps.get(1).y) as int;
}
