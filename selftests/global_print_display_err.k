// A Display implementation that prints: `println` holds the standard output lent while the
// formatter calls the implementation, and the implementation reaches it again by name.
#include <stdlib::io>
struct Loud { n: long }
methods Loud for Display {
    display &self w:Write -> void { println("inside"); writeTo(w, "{}", self.n); }
}
main -> int {
    l: Loud = Loud { n: 3 };
    println("{}", l);
    return 0;
}
