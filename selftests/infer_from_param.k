// A generic call standing as an argument takes the parameter's type as its destination, the way
// one stored into a declared variable does: a length parameter (`fixedOf`'s N, from getOr's key),
// a type parameter (`emptyVec`'s T), a macro's expansion (`vec![]`), and a weak literal's width
// (`vecOf(1, 2)` into a `Vec<long>` is a Vec<long>, not the Vec<int> its literals alone make).
// Through a method, a static method and a plain function. Exit 0 when all hold.
#include <stdlib::vec>
#include <stdlib::map>
#include <stdlib::fixedstring>

total v:Vec<long> -> long { s: long = 0; for x in v { s = s + x; } return s; }
struct Bag { items: Vec<long> }
methods Bag {
    put &self more:Vec<long> -> void { for x in more { self.items.push(x); } }
    make xs:Vec<long> -> Bag { return Bag { items: xs }; }
}

main -> int {
    m: HashMap<FixedString<16>, long> = map![];
    key: FixedString<16> = fixedOf("k");
    m.put(key, 7);
    if (m.getOr(fixedOf("k"), 0) != 7 || m.getOr(fixedOf("zz"), 3) != 3) { return 1; }
    if (total(emptyVec()) != 0 || total(vec![]) != 0) { return 2; }
    if (total(vec![5000000000, 1]) != 5000000001 || total(vecOf(1, 2)) != 3) { return 3; }
    b: Bag = Bag.make(vec![]);
    b.put(vec![4, 5]);
    if (b.items.len() != 2) { return 4; }
    return 0;
}
