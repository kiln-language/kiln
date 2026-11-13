// `for x in &v` lends each element; a scalar element is a copy, so there is nothing to lend.
#include <stdlib::vec>
twice<T> inout v:Vec<T> -> void { for x in &v { } }
main -> int { v: Vec<long>; v.push(1); twice(&v); return 0; }
