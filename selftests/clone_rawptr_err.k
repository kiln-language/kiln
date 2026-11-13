// An owning type that also holds a raw pointer: a field-wise copy would point at what the
// original does.
#include <stdlib::string>
struct Mixed { s: String, p: *u8 }
main -> int { m: Mixed = Mixed { s: stringOf("a"), p: 0 as *u8 }; c: Mixed = m.clone(); return c.s.len as int; }
