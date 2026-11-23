// A body's parameter seeds do not count toward its size (`copyableSize`): copied, each is a move
// that copy propagation removes. `Vec<T>.push` of a sum type that holds a `String` is 23
// instructions past its two seeds, and is copied into the loops that push, once the drop of the
// value it moved is gone before the inliner weighs it: the drop's flag test is a comparison of
// two constants once the flag's dead clearing is removed, and is decided then
// (`Opt.foldConstBranches`, `--no-refold`).
// ir-lacks: free_seeds::fill call vec::Vec_free_seeds::Val_push
// ir-lacks: free_seeds::fillText call vec::Vec_free_seeds::Val_push
#include <stdlib::{vec, string}>

enum Val { Null, Int(long), Text(String) }

fill n:long -> Vec<Val> {
    v: Vec<Val>;
    for i in 0..n { v.push(Val.Int(i * 3)); }
    return v;
}

fillText n:long -> Vec<Val> {
    v: Vec<Val>;
    for i in 0..n {
        s: String;
        s.pushLong(i);
        v.push(Val.Text(s));
    }
    return v;
}

main -> int {
    a: Vec<Val> = fill(1000);
    if (a.len() != 1000) { return 1; }
    sum: long = 0;
    for x in a { match x { Int(k) { sum = sum + k; } _ { return 2; } } }
    if (sum != 3 * 999 * 1000 / 2) { return 3; }
    b: Vec<Val> = fillText(300);
    if (b.len() != 300) { return 4; }
    chars: long = 0;
    for x in b { match x { Text(s) { chars = chars + s.len(); } _ { return 5; } } }
    if (chars != 10 + 90 * 2 + 200 * 3) { return 6; }
    return 0;
}
