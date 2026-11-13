// `&` of an immutable global is a lend that allows writing: refused.
#include <stdlib::vec>
bump inout v:Vec<long> -> void { v.push(9); }
mk -> Vec<long> { v: Vec<long>; return v; }
V: Vec<long> = mk();
main -> int { bump(&V); return 0; }
