// A `var` global lent to a function that walks its parameter is fine when nothing the walk calls
// writes that global: a writer of another global, a walk of a copy (batch 9's rule is no wider
// than the hazard). A writer of the global called after the walk, while the global is still lent,
// is refused by the law of exclusivity across the call (`global_lend_after_walk_err`).
#include <stdlib::{io, vec}>
var gV: Vec<long>;
var gW: Vec<long>;
var gCount: long = 0;
growW -> void { gW.push(3); }
bump -> void { gCount = gCount + 1; }
walkOther xs:&Vec<long> -> long { t: long = 0; for x in xs { growW(); bump(); t = t + x; } return t; }
main -> int {
    gV.push(1); gV.push(2);
    if (walkOther(gV) != 3 || gW.len() != 2 || gCount != 2) { return 1; }
    gV.push(4);
    copy: Vec<long> = gV.clone();
    if (walkOther(copy) != 7) { return 3; }
    return 0;
}
