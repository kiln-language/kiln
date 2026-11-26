// A view into a local kept where the caller can reach it: `out` belongs to the caller and
// outlives `buf`.
#include <stdlib::{io, vec, string}>
fill inout out:Vec<str> -> void { buf: Vec<u8>; buf.push(104); out.push(buf.asSlice() as str); }
main -> int { names: Vec<str>; fill(&names); println("{}", names.get(0)); return 0; }
