// A match arm borrowing into one field of a `var` global, calling a writer of that field.
#include <stdlib::{option, string}>
struct Reg { cur: Option<String>, count: long }
var gReg: Reg = Reg { cur: Option.None, count: 0 };
bump -> void { gReg.count = gReg.count + 1; }
reset -> void { gReg.cur = Option.None; }
main -> int {
    gReg.cur = Option.Some(stringOf("abc"));
    n: long = 0;
    match &gReg.cur { Some(s) { bump(); reset(); n = s.len; } None { } }
    return n as int;
}
