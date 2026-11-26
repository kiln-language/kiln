// A global outlives every caller, so it may hold only a view of static data or of a global's
// storage. `s` points at whatever the caller lent, here a local Vec released before the read.
#include <stdlib::{io, vec, string}>
var gstr: str = "";
keep s:str -> void { gstr = s; }
fill -> void { v: Vec<u8>; v.push(104); v.push(105); keep(v.asSlice() as str); }
main -> int { fill(); println("{}", gstr); return 0; }
