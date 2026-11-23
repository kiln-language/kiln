// A fn value reaches the functions whose address is taken at a type that fits its own. The float
// formatter a float's `any` box carries is addressed at no type: only `fmt.k`'s cast of the box's
// word calls it, so a typed fn value never reaches it, nor what it reaches (here a `Write` that
// pushes to the global the loop walks). Before, every fn value reached it and the loop was refused.
#include <stdlib::{io, string, vec}>

var gLog: Vec<long> = vec![];
struct LogW { n: long }
methods LogW for Write { write &self ptr:long len:long -> long { gLog.push(len); return len; } }

twice x:long -> long { return x * 2; }

main -> long {
    gLog.push(3);
    gLog.push(4);
    h: fn(long) -> long = &twice;
    s: long = 0;
    for x in gLog { s = s + h(x); }
    w: LogW = LogW { n: 0 };
    writeTo(w, "{}", 1.5);
    if (s != 14 || gLog.len() <= 2) { return 1; }
    return 0;
}
