// A safe function may not return a view into its own local: the Vec is released on the way out,
// and the caller would read freed memory.
#include <stdlib::{io, vec}>
leak -> [long] { v: Vec<long>; v.push(11); return v.asSlice(); }
main -> int { s: [long] = leak(); println("{}", s[0]); return 0; }
