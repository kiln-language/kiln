// An element of a borrowed slice handed to a parameter that takes it (`Vec.push`): both the
// slice's owner and the new vector would own one buffer. Refused (batch 9); it compiled, and the
// original string read another allocation's bytes after the copy was dropped.
#include <stdlib::{io, string, vec}>
copyFirst xs:[String] -> long { dst: Vec<String>; dst.push(xs[0]); return dst.len(); }
main -> int { src: Vec<String>; src.push(stringOf("a")); return copyFirst(src.asSlice()) as int; }
