// What the rule leaves alone: a body calling functions that read the walked `var` global, or write
// another one, and a function writing the global called after the loop. 6 + 6 + 10 = 22.
#include <stdlib::vec>
var gItems: Vec<long> = vec![1, 2, 3];
var gCount: long = 0;
total -> long { t: long = 0; for x in gItems { t = t + x; } return t; }
note x:long -> void { gCount = gCount + x; }
grow -> void { gItems.push(4); }
main -> int {
    t: long = 0;
    for x in gItems { t = t + total() / 3; note(x); }
    grow();
    return (t + gCount + total()) as int;
}
