// A match arm holding a borrow into a `var` global's payload calls a function that writes the
// global: what the binding points at could be released under it.
#include <stdlib::{option, string}>
var gName: Option<String> = Option.None;
reset -> void { gName = Option.None; }
main -> int {
    gName = Option.Some(stringOf("abc"));
    n: long = 0;
    match &gName { Some(s) { reset(); n = s.len; } None { } }
    return n as int;
}
