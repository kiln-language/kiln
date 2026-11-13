// A tuple's elements may be any type a struct field may be: Copy structs, owning structs, sum
// types, other tuples, `String`, `Vec`. A tuple is laid out as the struct of its elements would
// be, crosses a call as that struct would, owns what its elements own, and is released once, as a
// whole or element by element. Used here as a return, a parameter, a local, a struct field, a
// global (folded), an element of `Vec`/`Option`/`Result`, a `match` payload, and a generic
// function's parameter and result. Every release is counted.
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::option>
#include <stdlib::result>
#include <stdlib::string>

var gDrops: long = 0;
struct Res { n: long }
methods Res for Drop { drop &self -> void { gDrops = gDrops + self.n; } }
mk n:long -> Res { return Res { n: n }; }

struct P { x: long, y: long }
enum Shape { Dot, Box(long, long) }

pairOf a:long b:long -> (Res, long) { return (mk(a), b); }
copyPair -> (P, long) { return (P { x: 1, y: 2 }, 3); }
nested -> ((long, int), (P, u8)) { return ((4, 5 as int), (P { x: 6, y: 7 }, 8 as u8)); }
peek t:(Res, long) -> long { return t.0.n + t.1; }          // a read borrow
keep sink t:(Res, long) -> long { return t.1; }            // takes it: released here
swap<A, B> a:A b:B -> (B, A) { return (b, a); }
firstOf<A, B> t:(A, B) -> A { return t.0; }

struct Holder { pair: (Res, String), k: long }

shapes -> (Shape, Shape) { return (Shape.Box(2, 3), Shape.Dot); }
area s:Shape -> long { match s { Box(w, h) { return w * h; } Dot { return 0; } } }

folded -> long {
    v: Vec<(long, String)>;
    v.push((5, stringOf("abc")));
    t: (long, String) = v.pop();
    q: ((long, long), P) = ((1, 2), P { x: 3, y: 4 });
    return t.0 + t.1.len + q.0.1 + q.1.x;
}
gFolded: long = folded();
gPair: (long, long) = (40, 2);

main -> int {
    // Copy elements, nested, by value.
    c: (P, long) = copyPair();
    if (c.0.x + c.0.y + c.1 != 6) { return 1; }
    n: ((long, int), (P, u8)) = nested();
    if (n.0.0 + n.0.1 + n.1.0.y + (n.1.1 as long) != 24) { return 2; }
    if (sizeof((P, long)) != 24 || sizeof((u8, long)) != 16) { return 3; }

    // Owning elements: released once, wherever the tuple ends.
    {
        t: (Res, long) = pairOf(1, 2);
        if (peek(t) != 3) { return 4; }
        if (keep(pairOf(10, 7)) != 7) { return 5; }
    }
    if (gDrops != 11) { return 6; }
    gDrops = 0;
    {
        h: Holder = Holder { pair: (mk(100), stringOf("hi")), k: 1 };
        if (h.pair.0.n + h.pair.1.len != 102) { return 7; }
    }
    if (gDrops != 100) { return 8; }
    gDrops = 0;

    // In containers.
    {
        v: Vec<(Res, long)>;
        v.push(pairOf(1000, 1));
        v.push((mk(2000), 2));
        if (v.len() != 2 || v[1].0.n != 2000) { return 9; }
        o: Option<(Res, String)> = Option.Some((mk(30000), stringOf("x")));
        match o { Some(z) { if (z.0.n != 30000 || z.1.len != 1) { return 10; } } None { return 11; } }
        r: Result<(Res, long), long> = Result.Ok(pairOf(400000, 4));
        match r { Ok(z) { if (z.1 != 4) { return 12; } } Err(e) { return 13; } }
    }
    if (gDrops != 433000) { return 14; }
    gDrops = 0;

    // Sum types as elements, and a `for` over a Vec of tuples.
    s: (Shape, Shape) = shapes();
    if (area(s.0) + area(s.1) != 6) { return 15; }
    {
        w: Vec<(String, long)>;
        w.push((stringOf("ab"), 1));
        w.push((stringOf("cde"), 2));
        tot: long = 0;
        for p in w { tot = tot + p.0.len + p.1; }
        if (tot != 8) { return 16; }
        cl: (String, long) = w[0].clone();
        if (cl.0.len != 2) { return 17; }
    }

    // Generic: inferred from the arguments and from the destination.
    g: (long, P) = swap(P { x: 11, y: 12 }, 13);
    if (g.0 != 13 || g.1.y != 12) { return 18; }
    {
        gr: (long, Res) = swap(mk(5000000), 9);
        if (firstOf(gr) != 9) { return 19; }
    }
    if (gDrops != 5000000) { return 20; }

    // Equality, and the folded globals.
    if (!((1, P { x: 2, y: 3 }) == (1, P { x: 2, y: 3 }))) { return 21; }
    if (gFolded != 13 || gPair.0 + gPair.1 != 42) { return 22; }
    println("ok");
    return 0;
}
