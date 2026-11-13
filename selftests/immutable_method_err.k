// A method the guard proves writes its receiver (push stores through self) is refused on an immutable global;
// one that only reads (get, len) is not.
#include <stdlib::vec>
mk -> Vec<long> { v: Vec<long>; v.push(1); return v; }
V: Vec<long> = mk();
main -> int { n: long = V.len() + V.get(0); V.push(2); return n as int; }
