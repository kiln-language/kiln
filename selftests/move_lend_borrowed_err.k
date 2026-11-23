// A borrow a call returned is a lend of what that call borrowed: `v.at(0)` points into `v`'s
// buffer, which `take` may release.
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::string>
take r:String sink v:Vec<String> -> void { println("{}", r); }
main -> int { v: Vec<String>; v.push(format("hello")); take(v.at(0), v); return 0; }
