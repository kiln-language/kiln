// A tuple is a struct of its elements to `stdlib::reflect`, so the `Encode`/`Decode` derives
// write one for it as for any struct: each element in order. A tuple field, a `Vec` of tuples,
// and a tuple encoded on its own, all round-tripped.
#include <stdlib::io>
#include <stdlib::encode>
#include <stdlib::string>
#include <stdlib::vec>
#include <stdlib::result>

struct P { x: long, y: long }
struct Rec { name: String, pos: (P, long), pairs: Vec<(long, String)> }

main -> int {
    v: Vec<(long, String)>;
    v.push((1, stringOf("a")));
    v.push((2, stringOf("bc")));
    r: Rec = Rec { name: stringOf("rec"), pos: (P { x: 3, y: -4 }, 5), pairs: v };
    bytes: Vec<u8> = encodeValue(r);
    view: [u8] = "";
    unsafe { view = bytesOf(&bytes); }
    back: Result<Rec, str> = decodeValue(view);
    match back {
        Ok(q) {
            if (q.name.len != 3 || q.pos.0.x != 3 || q.pos.0.y != -4 || q.pos.1 != 5) { return 1; }
            if (q.pairs.len() != 2 || q.pairs[1].0 != 2 || q.pairs[1].1.len != 2) { return 2; }
        }
        Err(e) { return 3; }
    }
    t: (long, (u8, String)) = (-9, (7 as u8, stringOf("xyz")));
    b2: Vec<u8> = encodeValue(t);
    // zigzag(-9) is one byte, the u8 one, the String a length and three bytes.
    if (b2.len() != 6) { return 4; }
    v2: [u8] = "";
    unsafe { v2 = bytesOf(&b2); }
    t2: Result<(long, (u8, String)), str> = decodeValue(v2);
    match t2 {
        Ok(z) { if (z.0 != -9 || z.1.0 != 7 as u8 || z.1.1.len != 3) { return 5; } }
        Err(e) { return 6; }
    }
    println("ok");
    return 0;
}
