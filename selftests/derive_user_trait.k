// `derive` is not specific to Encode: any trait may name a macro that writes its implementation
// for a type that has none. This test declares two traits with their macros. `Weigh` is an
// instance method summed over every field, and over a sum type's tag and live payloads; its macro
// takes a `Decl`, so it gets either kind of type. `Zero` is a static method that builds a value
// field by field; its macro takes a `Struct`. The derives are asked for in four ways: a method
// call, a static call, a field of a derived type (so one derive asks for the next), and a value
// made into a trait object. A generic struct is derived per instance: `Pair<long, Inner>` is
// handed over with its fields at their concrete types. Exit 0 when every check holds, otherwise
// the number of the first that did not.
#include <stdlib::ast>
#include <stdlib::reflect>
#include <stdlib::vec>

pub trait Weigh derive deriveWeigh { weight &self -> long; }
pub trait Zero derive deriveZero { zero -> Self; }

methods long for Weigh { weight &self -> long { return self; } }
methods long for Zero { zero -> long { return 0; } }

pub macro deriveWeigh d:Decl -> Node {
    r: Node = Node.Nothing;
    match d {
        OfStruct(t) { r = weighStruct(t); }
        OfEnum(e)   { r = weighEnum(e); }
    }
    return r;
}
local weighStruct t:Struct -> Node {
    terms: Vec<Node>;
    for i in 0..t.fields.len() {
        f: Field = t.fields.get(i);
        terms.push(quote { w = w + self.@(f.name).weight(); });
    }
    return quote { methods @(t.name) for Weigh { weight &self -> long { w: long = 0; @terms return w; } } };
}
// A thousand per tag, plus the live variant's payloads.
local weighEnum e:Enum -> Node {
    arms: Vec<Node>;
    for i in 0..e.variants.len() {
        ps: Vec<Node>;
        for j in 0..e.variants.at(i).payloads.len() {
            p: Field = e.variants.at(i).payloads.get(j);
            ps.push(quote { w = w + self.@(p.name).weight(); });
        }
        which: Node = Node.Int(e.variants.at(i).tag);
        arms.push(quote { if (tag == @which) { @ps } });
    }
    return quote { methods @(e.name) for Weigh {
        weight &self -> long { tag: long = self.@(e.tagField) as long; w: long = tag * 1000; @arms return w; }
    } };
}

pub macro deriveZero t:Struct -> Node {
    names: Vec<str>;
    vals: Vec<Node>;
    for i in 0..t.fields.len() {
        f: Field = t.fields.get(i);
        names.push(f.name);
        vals.push(quote { @(Node.Name(f.typeName)).zero() });
    }
    built: Node = Node.StructLit(t.name, names, vals);
    return quote { methods @(t.name) for Zero { zero -> Self { return @built; } } };
}

struct Pair<A, B> { a: A, b: B }
struct Inner { x: long, y: long }
struct Outer { i: Inner, p: Pair<long, Inner>, k: long }
pub enum Ev { Quit, Move(long, long), Hit(Inner) }
struct Solo { n: long }

local total w:Weigh -> long { return w.weight(); }

main -> int {
    o: Outer = Outer { i: Inner { x: 1, y: 2 }, p: Pair { a: 10, b: Inner { x: 100, y: 200 } }, k: 5000 };
    if (o.weight() != 5313) { return 1; }
    z: Outer = Outer.zero();
    if (z.weight() != 0 || z.p.b.y != 0) { return 2; }
    e: Ev = Ev.Move(3, 4);
    if (e.weight() != 1007) { return 3; }
    h: Ev = Ev.Hit(Inner { x: 1, y: 1 });
    if (h.weight() != 2002) { return 4; }
    s: Solo = Solo { n: 9 };
    if (total(s) != 9) { return 5; }
    return 0;
}
