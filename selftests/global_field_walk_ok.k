// A walk of one field of a `var` global may call what writes another field of it: the rule
// against changing a collection while it is walked judges the global field by field. Through a
// function, a method of the global, a lend of the field to a function that walks it, a borrowed
// match arm, and a field two levels down.
#include <stdlib::{io, option, string, vec}>

struct Inner { a: Vec<long>, n: long }
struct Reg { items: Vec<long>, count: long, log: Vec<long>, inner: Inner, cur: Option<String> }
var gReg: Reg = Reg { items: vec![1, 2, 3], count: 0, log: vec![],
                      inner: Inner { a: vec![4, 5], n: 0 }, cur: Option.None };

bump -> void { gReg.count = gReg.count + 1; }
note x:long -> void { gReg.log.push(x); }
tallyInner -> void { gReg.inner.n = gReg.inner.n + 1; }
methods Reg {
    tick &self -> void { self.count = self.count + 10; }
}

// walks the field it is lent, while calling writers of other fields
walk xs:&Vec<long> -> long { t: long = 0; for x in xs { bump(); note(x); t = t + x; } return t; }

main -> int {
    t: long = 0;
    for x in gReg.items { bump(); note(x); gReg.tick(); t = t + x; }
    if (t != 6 || gReg.count != 33 || gReg.log.len() != 3) { return 1; }
    for y in gReg.inner.a { tallyInner(); bump(); t = t + y; }
    if (t != 15 || gReg.inner.n != 2 || gReg.count != 35) { return 2; }
    if (walk(gReg.items) != 6 || gReg.count != 38 || gReg.log.len() != 6) { return 3; }
    gReg.cur = Option.Some(stringOf("abc"));
    n: long = 0;
    match &gReg.cur { Some(s) { bump(); note(7); n = s.len; } None { } }
    if (n != 3 || gReg.count != 39 || gReg.log.len() != 7) { return 4; }
    println("global_field_walk_ok");
    return 0;
}
