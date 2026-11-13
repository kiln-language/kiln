// The shapes the compiler's own `.klib` metadata is made of, round-tripped through the derived
// codecs (packages part 2): a name that is a typed integer (`enum Sym: long { }`) whose
// hand-written codec goes through a string table held in globals, the way the compiler's
// interner indices do; a node struct holding names, indices, backed enums and a sum type of
// index payloads; a `Vec` of those; and negative longs (-1 is "no node"). Re-encoding the decoded
// value must give the same bytes. Exit 0 when every check holds, otherwise the number of the
// first that did not.
#include <stdlib::encode>
#include <stdlib::map>

pub enum Sym: long { }
pub NO_SYM: Sym = -1;

// The process's names, and the table one encoding writes them through: a name is written as its
// table position + 1 (0 is no name), and the table is written once, beside the values.
var gText: Vec<str> = vec![];
var gOut: Vec<long> = vec![];        // by Sym: its table position, or -1
var gTable: Vec<str> = vec![];
var gIn: Vec<Sym> = vec![];          // by table position: the name it reads back as

local internName s:str -> Sym {
    for i in 0..gText.len() { if (gText.get(i) == s) { return i as Sym; } }
    gText.push(s);
    return (gText.len() - 1) as Sym;
}

methods Sym for Encode {
    encode &self out:&Encoder -> void {
        n: long = self as long;
        if (n < 0) { out.putUvarint(0); return; }
        while (gOut.len() <= n) { gOut.push(-1); }
        if (gOut.get(n) < 0) { gOut.set(n, gTable.len()); gTable.push(gText.get(n)); }
        out.putUvarint((gOut.get(n) + 1) as u64);
    }
}
methods Sym for Decode {
    decode inp:&Decoder -> Sym {
        t: long = inp.getUvarint() as long;
        if (t == 0) { return NO_SYM; }
        if (t > gIn.len()) { inp.fail("a name past the string table"); return NO_SYM; }
        return gIn.get(t - 1);
    }
}

pub enum Op: int { Add, Sub, Call, Name, Lit }
pub enum Kind: int { Int, Long, Struct, Void }
pub enum Payload { None, Num(long), Text(Sym), Name(Sym), Call(long), Sub(long) }
pub struct Expr { op: Op, left: long, right: long, kind: Kind, structName: Sym, isParen: bool, payload: Payload }
pub struct Call { name: Sym, receiver: long, firstArg: long, argCount: long, slot: long }
pub struct Chunk { exprs: Vec<Expr>, calls: Vec<Call>, args: Vec<long>, names: Vec<Sym> }

local sameBytes a:Vec<u8> b:Vec<u8> -> bool {
    if (a.len() != b.len()) { return false; }
    for i in 0..a.len() { if (a.get(i) != b.get(i)) { return false; } }
    return true;
}

main -> int {
    foo: Sym = internName("foo");
    bar: Sym = internName("mod::bar");
    internName("unused");
    c: Chunk = Chunk { exprs: vec![], calls: vec![], args: vec![], names: vec![] };
    c.exprs.push(Expr { op: Op.Name, left: -1, right: -1, kind: Kind.Long, structName: NO_SYM,
                        isParen: false, payload: Payload.Name(foo) });
    c.exprs.push(Expr { op: Op.Lit, left: -1, right: -1, kind: Kind.Int, structName: NO_SYM,
                        isParen: true, payload: Payload.Num(-9223372036854775807 - 1) });
    c.exprs.push(Expr { op: Op.Add, left: 0, right: 1, kind: Kind.Long, structName: bar,
                        isParen: false, payload: Payload.None });
    c.exprs.push(Expr { op: Op.Call, left: -1, right: -1, kind: Kind.Struct, structName: bar,
                        isParen: false, payload: Payload.Call(0) });
    c.exprs.push(Expr { op: Op.Sub, left: -1, right: -1, kind: Kind.Void, structName: NO_SYM,
                        isParen: false, payload: Payload.Sub(2) });
    c.calls.push(Call { name: bar, receiver: -1, firstArg: 0, argCount: 2, slot: -2 });
    c.args.push(2);
    c.args.push(4);
    c.names.push(foo);
    c.names.push(NO_SYM);

    first: Vec<u8> = encodeValue(c);
    // Two names were written, in order of first use; the third never was.
    if (gTable.len() != 2 || gTable.get(0) != "foo" || gTable.get(1) != "mod::bar") { return 1; }

    // Read back as another process would: its own interner, already holding other names, so
    // every name has to come back through the table and not as the number it was.
    gText.clear();
    internName("other");
    for i in 0..gTable.len() { gIn.push(internName(gTable.get(i))); }
    view: [u8] = "";
    unsafe { view = bytesOf(&first); }
    back: Result<Chunk, str> = decodeValue(view);
    if (!back.isOk()) { return 2; }
    d: Chunk = back.unwrap();
    if (d.exprs.len() != 5 || d.calls.len() != 1 || d.args.len() != 2 || d.names.len() != 2) { return 3; }
    e0: Expr = d.exprs.get(0);
    match e0.payload { Name(s) { if (gText.get(s as long) != "foo") { return 4; } } _ { return 4; } }
    e1: Expr = d.exprs.get(1);
    match e1.payload { Num(v) { if (v != -9223372036854775807 - 1) { return 5; } } _ { return 5; } }
    if (!e1.isParen || e1.kind != Kind.Int || e1.left != -1) { return 6; }
    e2: Expr = d.exprs.get(2);
    if (e2.op != Op.Add || e2.right != 1 || gText.get(e2.structName as long) != "mod::bar") { return 7; }
    if (d.calls.get(0).slot != -2 || d.calls.get(0).name != e2.structName) { return 8; }
    if (d.names.get(1) != NO_SYM || d.args.get(1) != 4) { return 9; }

    // Re-encoded through a fresh table, the decoded value writes the same bytes.
    gOut.clear();
    gTable.clear();
    again: Vec<u8> = encodeValue(d);
    if (!sameBytes(first, again)) { return 10; }

    // Damaged input is refused, not trusted: a truncated chunk, and a name past the table.
    short: [u8] = view[0..view.len - 1];
    cut: Result<Chunk, str> = decodeValue(short);
    if (cut.isOk()) { return 11; }
    bad: Vec<u8> = vec![u8: 9];
    bv: [u8] = "";
    unsafe { bv = bytesOf(&bad); }
    s: Result<Sym, str> = decodeValue(bv);
    if (s.isOk()) { return 12; }
    return 0;
}
