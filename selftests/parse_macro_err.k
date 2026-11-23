#include <stdlib::{io, ast}>

// A macro is read after every module, so an error in one is reported after the rest of the file's,
// and each macro is gone on from like any declaration.

macro twice e:Node -> Node { x: long = ; return e; }

macro thrice e:Node -> Node { return quote { @(e) * 3 } }

f -> long { return 1 }

main -> long { return thrice!(2) + f(); }
