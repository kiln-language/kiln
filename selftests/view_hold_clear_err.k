// Clearing a Vec of Strings releases each one, and `s` views the first.
#include <stdlib::{io, vec, string}>
main -> int {
    names: Vec<String>;
    names.push(stringOf("hello"));
    s: str = names.at(0).slice(0, 2);
    names.clear();
    println("{}", s);
    return 0;
}
