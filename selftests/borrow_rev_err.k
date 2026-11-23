// The left operand's type answers `==`: `Tag` implements `Eq<str>` but `str` has no `Eq<Tag>`,
// so `"center" == w` with `w: &Tag` is refused (not compared as addresses), while `w == "center"`
// is `Tag`'s own comparison.
#include <stdlib::string>
struct Tag { s: String }
methods Tag for Eq<str> { eq &self other:str -> bool { unsafe { return strEq(self.s.view(), other); } } }
fwd w:&Tag -> int { if (w == "center") { return 1; } return 0; }
rev w:&Tag -> int { if ("center" == w) { return 1; } return 0; }
main -> int { t: Tag = Tag { s: stringOf("center") }; return fwd(&t) + rev(&t); }
