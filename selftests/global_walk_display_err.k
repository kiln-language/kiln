// A Display implementation that writes the global a loop walks: `println` reaches it through the
// formatter, which calls the vtable slot a box holds through a fn value made of the raw word, so
// every implementation the compiler placed in a vtable that fits is reached.
#include <stdlib::{io, vec}>
struct Item { n: long }
var gItems: Vec<Item>;
methods Item for Display {
    display &self w:Write -> void { gItems.push(Item { n: self.n + 1 }); writeTo(w, "{}", self.n); }
}
main -> int {
    gItems.push(Item { n: 1 });
    for x in gItems { println("{}", x); }
    return 0;
}
