// A macro is written against `Node` without this file including `ast`: a program that declares
// a macro has `stdlib::ast` in it, its names are visible from anywhere, and the declaration is
// read once the whole program has been -- which is what lets `vec.k` hold `vec!` although `ast`
// is built on `Vec`. Exit code 6.
#include <stdlib::vec>
main -> int { v: Vec<long> = twice![3]; return (v.get(0) + v.get(1)) as int; }
macro twice src:str -> Node {
    e: Node = parseExpr(src);
    items: Vec<Node>;
    items.push(e.clone());
    items.push(e);
    return Node.Call("vecOf", items);
}
