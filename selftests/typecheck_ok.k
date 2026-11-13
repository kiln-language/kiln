// The shapes the new argument, assignment and return checks must NOT refuse. Each one was a
// false positive during the work and is here so it stays fixed.
#include <stdlib::io>
#include <stdlib::heap>
#include <stdlib::vec>

enum Access: int { Read, Write }           // a BACKED enum: an integer that names its enum
struct Box2 { a: long, b: long }

local narrow b:u8 -> long { return b as long; }          // an untyped literal takes the width
local mode m:Access -> long { return m as long; }        // a backed enum passes as itself
local fill inout v:Vec<long> n:long -> void { v.push(n); }
local size2 -> long { return sizeof(Box2); }             // sizeof carries the type it MEASURES
local rest fmt:str vs:...long -> long { return vs.len; } // a variadic sets a floor, not a count

// Every path exits: an if-chain ending in a bare else, and a loop with no break.
local pick n:long -> long {
    if (n > 0) { return 1; } else if (n < 0) { return 2; } else { return 3; }
}
local spin n:long -> long {
    loop { if (n > 0) { return n; } n = n + 1; }
}

main -> int {
    t: long = 0;
    t = t + narrow(200);                    // weak literal into a u8
    t = t + mode(Access.Write);             // backed enum argument
    v: Vec<long> = vec![];
    fill(&v, 7);                            // a lend, matched against the lent value
    t = t + v.len();
    t = t + size2();                        // 16
    t = t + rest("x", 1, 2, 3);             // 3
    t = t + pick(-5);                       // 2
    t = t + spin(4);                        // 4
    unsafe { p: long = &v; if (p != 0) { t = t + 1; } }   // an address, inside unsafe
    println("{}", t);
    return t as int;
}
