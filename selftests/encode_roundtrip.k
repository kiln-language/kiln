// `Encode`/`Decode` with nothing written by hand: every implementation below is the derive's
// (stdlib/encode.k), made the first time `main` needs it: a nested struct, a `Vec` of structs,
// `Option`s, a `HashMap`, a sum type with payloads, a backed enum, a generic struct's instance,
// negative and extreme integers, a `str` decoded as a view into the input. Then the failures:
// a truncated input and an invalid variant tag are refused cleanly, not trapped on. Exit 0 when
// every check holds, otherwise the number of the first that did not.
#include <stdlib::io>
#include <stdlib::encode>
#include <stdlib::map>
#include <stdlib::option>
#include <stdlib::bytes>

pub enum Color: int { Red, Green = 5, Blue }
pub enum Shape { Dot, Circle(long), Rect(long, long), Named(String, Color) }

struct Line { a: long, b: long, c: Color }
struct Pair<A, B> { first: A, second: B }
struct Doc {
    id: long,
    title: String,
    lines: Vec<Line>,
    note: Option<String>,
    none: Option<long>,
    counts: HashMap<str, long>,
    shapes: Vec<Shape>,
    pair: Pair<long, String>,
    low: long,
    high: long,
    small: i16,
    unsigned: u32,
    flag: bool
}

local radius s:Shape -> long {
    out: long = -1;
    match s { Circle(r) { out = r; } _ { } }
    return out;
}
local area s:Shape -> long {
    out: long = 0;
    match s { Rect(w, h) { out = w * h; } _ { } }
    return out;
}

main -> int {
    d: Doc = Doc { id: 7, title: stringOf("hello"), lines: vec![], note: Option.Some(stringOf("n")),
                   none: Option.None, counts: map![], shapes: vec![],
                   pair: Pair { first: -1, second: stringOf("two") },
                   low: -9223372036854775807 - 1, high: 9223372036854775807, small: -300,
                   unsigned: 4000000000 as u32, flag: true };
    d.lines.push(Line { a: 1, b: -2, c: Color.Green });
    d.lines.push(Line { a: 300, b: 70000, c: Color.Blue });
    d.counts.put("x", 1);
    d.counts.put("yy", -2);
    d.shapes.push(Shape.Dot);
    d.shapes.push(Shape.Circle(5));
    d.shapes.push(Shape.Rect(-3, 4));
    d.shapes.push(Shape.Named(stringOf("tri"), Color.Blue));

    e: Encoder;
    d.encode(e);
    bytes: Vec<u8> = e.bytes();
    view: [u8] = "";
    unsafe { view = bytesOf(&bytes); }

    dd: Decoder;
    unsafe { dd = decoderOf(view); }
    r: Doc = Doc.decode(dd);
    if (!dd.done()) { return 1; }
    if (r.id != 7 || r.title != "hello") { return 2; }
    if (r.lines.len() != 2 || r.lines.at(0).b != -2 || r.lines.at(1).b != 70000) { return 3; }
    if (r.lines.at(0).c != Color.Green || r.lines.at(1).c != Color.Blue) { return 4; }
    if (!r.note.isSome() || r.none.isSome()) { return 5; }
    if (r.counts.len() != 2 || r.counts.get("x") != 1 || r.counts.get("yy") != -2) { return 6; }
    if (r.pair.first != -1 || r.pair.second != "two") { return 7; }
    if (r.low != -9223372036854775807 - 1 || r.high != 9223372036854775807 || r.small != -300) { return 8; }
    if (r.unsigned != 4000000000 as u32 || !r.flag) { return 9; }
    if (r.shapes.len() != 4 || nameof(Shape, r.shapes.at(0)) != "Dot") { return 10; }
    if (nameof(Shape, r.shapes.at(3)) != "Named") { return 11; }
    // Everything, byte for byte: what was decoded encodes to exactly what it was decoded from.
    again: Vec<u8> = encodeValue(r);
    av: [u8] = "";
    unsafe { av = bytesOf(&again); }
    if (!bytesEqual(av, view)) { return 19; }
    shape3: Shape = r.shapes.pop();
    if (area(r.shapes.pop()) != -12 || radius(r.shapes.pop()) != 5) { return 20; }

    // Zigzag: -1 and 1 are one byte each, -64 one byte, 64 two.
    if (encodeValue(-1 as long).len() != 1 || encodeValue(-64 as long).len() != 1 || encodeValue(64 as long).len() != 2) { return 12; }
    // A str decodes as a view into the input, not a copy.
    sb: Vec<u8> = encodeValue("abc");
    sv: [u8] = "";
    unsafe { sv = bytesOf(&sb); }
    sd: Decoder;
    unsafe { sd = decoderOf(sv); }
    s: str = str.decode(sd);
    if (s != "abc") { return 13; }
    unsafe { if (s.ptr != sv.ptr + 1) { return 14; } }

    // Truncated: refused, with the first reason, and nothing read past the end.
    short: Decoder;
    unsafe { short = decoderOf(view[..10]); }
    bad: Doc = Doc.decode(short);
    if (short.ok() || short.error() != "unexpected end of input") { return 15; }
    // A tag no variant of Shape has.
    tb: Vec<u8> = encodeValue(9 as long);
    tv: [u8] = "";
    unsafe { tv = bytesOf(&tb); }
    res: Result<Shape, str> = decodeValue(tv);
    match res { Ok(_) { return 16; } Err(why) { if (why != "invalid variant tag") { return 17; } } }
    // The whole thing through the one-shot helper.
    whole: Result<Doc, str> = decodeValue(view);
    if (!whole.isOk()) { return 18; }
    println("round trip of {} bytes holds", bytes.len());
    return 0;
}
