// The same with the `sink` inferred: `take` keeps `s`, so it takes it.
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::string>
var gKeep: Vec<String>;
take r:String s:String -> void { println("{}", r); gKeep.push(s); }
main -> int { x: String = format("hello"); take(x, x); return 0; }
