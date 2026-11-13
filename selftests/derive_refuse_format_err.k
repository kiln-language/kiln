// A derive macro refuses with a message `format` built.
#include <stdlib::ast>
#include <stdlib::reflect>
#include <stdlib::string>
pub trait Plain derive derivePlain { plain &self -> long; }
pub macro derivePlain t:Struct -> Node {
    for i in 0..t.fields.len() {
        f: Field = t.fields.get(i);
        if (f.isRawPointer) { refuse(format("{}.{} is a raw pointer (field {} of {})", t.name, f.name, i, t.fields.len())); }
    }
    return quote { methods @(t.name) for Plain { plain &self -> long { return 1; } } };
}
struct Node2 { a: long, next: *long }
main -> int { n: Node2 = Node2 { a: 1, next: 0 as *long }; return n.plain() as int; }
