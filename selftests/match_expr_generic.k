// A match on an expression inside a generic function (stamped per instance), and in code the
// compiler runs: a global's initializer.
#include <stdlib::{core, vec, option}>
firstOr<T: Copy> v:Vec<Option<T>> alt:T -> T {
    match v.at(0) { Some(x) { return x; } None { return alt; } }
}
pick n:long -> Option<long> { if (n > 2) { return Option.Some(n * 10); } return Option.None; }
classify -> long {
    t: long = 0;
    for i in 0..5 { match pick(i) { Some(x) { t = t + x; } None { t = t + 1; } } }
    return t;               // 1 + 1 + 1 + 30 + 40 = 73
}
G: long = classify();
main -> int {
    v: Vec<Option<long>> = vec![];
    v.push(Option.Some(7));
    w: Vec<Option<u8>> = vec![];
    w.push(Option.None);
    return (G + firstOr(v, 0) + firstOr(w, 2 as u8) as long) as int;    // 73 + 7 + 2 = 82
}
