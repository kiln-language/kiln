// A trait object over a temporary, stored in a global: the temporary's slot is reused once the
// function returns.
#include <stdlib::{io, write}>
var gw: Write = FileOut { fd: 1 };
set -> void { gw = FileOut { fd: 2 }; }
main -> int { set(); return 0; }
