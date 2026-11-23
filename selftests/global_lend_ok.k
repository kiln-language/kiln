// What the law of exclusivity across a call still allows for a `var` global lent to it: another
// field written by name, the global read by name under a read lend, another field read under an
// `inout` lend, writes through the parameter itself, a copy handed over, a writer called before or
// after the call, a scalar passed by value, another global written, a `&self` method that reads
// the global by name, and a fn value of a type no writer of the global fits.
#include <stdlib::{io, vec}>
struct Reg { items: Vec<long>, count: long, total: long }
var gReg: Reg = Reg { items: vec![1, 2, 3], count: 0, total: 7 };
var gOther: Reg = Reg { items: vec![], count: 0, total: 0 };
var gN: long = 4;
struct Pt { x: long, y: long }
var gPt: Pt = Pt { x: 1, y: 2 };

bumpCount -> void { gReg.count = gReg.count + 1; }
readTotal -> long { return gReg.total; }
bumpOther -> void { gOther.count = gOther.count + 1; }
setN -> void { gN = 100; }

// lent to read: writes of another field, reads of anything, writes of another global
sum xs:&Vec<long> -> long { t: long = 0; for x in xs { bumpCount(); bumpOther(); t = t + x + readTotal() - 7; } return t; }
// lent inout: reads and writes of another field by name, and writes through the parameter
grow inout xs:Vec<long> -> void { xs.push(gReg.total); bumpCount(); }
// a copy: the callee writes its own
copyIn sink r:Reg -> long { bumpCount(); r.count = r.count + 50; return r.count; }
// plain data handed to a `sink`: the callee's own copy, whatever happens to the global
takeCopy sink p:Pt -> long { gPt.x = 9; p.y = p.y + 1; return p.x + p.y; }
// a scalar by value
plus n:long -> long { setN(); return n + 1; }
// a fn value of one type reaches only the addressed functions of that type: `clearAll` writes the
// global, but a `fn(long) -> long` cannot hold it
clearAll -> void { gOther.total = 0; gReg.count = 0; }
double x:long -> long { return x * 2; }
var gDone: fn() -> void = &clearAll;
var gTwice: fn(long) -> long = &double;
scaled r:Reg -> long { return gTwice(r.total); }
methods Reg {
    // a read-only method may read the global it was called on by name
    peek &self -> long { return self.total + readTotal(); }
    // a method writing `self` may write through `self`
    add &self v:long -> void { self.total = self.total + v; }
}

main -> int {
    if (sum(gReg.items) != 6 || gReg.count != 3 || gOther.count != 3) { return 1; }
    grow(&gReg.items);
    if (gReg.items.len() != 4 || gReg.items[3] != 7 || gReg.count != 4) { return 2; }
    if (copyIn(gReg.clone()) != 54 || gReg.count != 5) { return 3; }
    if (takeCopy(gPt) != 4 || gPt.x != 9) { return 7; }
    bumpCount();
    if (plus(gN) != 5 || gN != 100) { return 4; }
    if (gReg.peek() != 14) { return 5; }
    gReg.add(3);
    bumpCount();
    if (gReg.total != 10 || gReg.count != 7) { return 6; }
    if (scaled(gReg) != 20) { return 8; }
    gDone();
    if (gReg.count != 0) { return 9; }
    println("global_lend_ok");
    return 0;
}
