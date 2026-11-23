// A hand-written implementation wins over the derive, wherever it is met: here on a backed enum
// used as a typed integer (`Sym`, an empty `enum Sym: long { }`), whose codec writes the number
// biased by 1000, and on a struct (`Secret`) that writes only one of its fields. Both are
// reached from inside DERIVED code (`Rec`'s fields, `Vec<Rec>`'s elements, `Tok`'s payloads),
// so the check is that the derive calls them rather than deriving its own. The exact bytes are
// checked, which also pins the format: zigzag LEB128 for a signed integer, LEB128 for a length
// and a tag. Exit 0 when every check holds, otherwise the number of the first that did not.
#include <stdlib::encode>

pub enum Sym: long { }
methods Sym for Encode { encode &self out:&Encoder -> void { out.putVarint((self as long) + 1000); } }
methods Sym for Decode { decode inp:&Decoder -> Sym { return (inp.getVarint() - 1000) as Sym; } }

struct Secret { shown: long, hidden: long }
methods Secret for Encode { encode &self out:&Encoder -> void { out.putVarint(self.shown); } }
methods Secret for Decode { decode inp:&Decoder -> Secret { return Secret { shown: inp.getVarint(), hidden: -1 }; } }

struct Rec { name: Sym, delta: long, s: Secret }
pub enum Tok { End, Word(Sym, long), Pair(Rec, Rec) }

local same got:Vec<u8> want:Vec<u8> -> bool {
    if (got.len() != want.len()) { return false; }
    for i in 0..got.len() { if (got.get(i) != want.get(i)) { return false; } }
    return true;
}

main -> int {
    // Sym 5 -> 1005 -> zigzag 2010 = 218 15; delta -3 -> 5; Secret writes 7 -> 14 only.
    r: Rec = Rec { name: 5 as Sym, delta: -3, s: Secret { shown: 7, hidden: 99 } };
    want: Vec<u8> = vec![u8: 218, 15, 5, 14];
    if (!same(encodeValue(r), want)) { return 1; }

    v: Vec<Rec>;
    v.push(r);
    v.push(Rec { name: 0 as Sym, delta: 64, s: Secret { shown: -1, hidden: 0 } });
    // A length of 2, then each Rec: 1000 -> 208 15, 64 -> 128 1, -1 -> 1.
    wantV: Vec<u8> = vec![u8: 2, 218, 15, 5, 14, 208, 15, 128, 1, 1];
    if (!same(encodeValue(v), wantV)) { return 2; }

    // A sum type: the tag (LEB128), then the payloads.
    t: Tok = Tok.Word(3 as Sym, -2);
    wantT: Vec<u8> = vec![u8: 1, 214, 15, 3];
    if (!same(encodeValue(t), wantT)) { return 3; }

    // Back again, through the hand-written decoders.
    bytes: Vec<u8> = encodeValue(v);
    view: [u8] = "";
    unsafe { view = bytesOf(&bytes); }
    back: Result<Vec<Rec>, str> = decodeValue(view);
    if (!back.isOk()) { return 4; }
    w: Vec<Rec> = back.unwrap();
    if (w.len() != 2 || w.at(0).name as long != 5 || w.at(1).delta != 64) { return 5; }
    if (w.at(0).s.shown != 7 || w.at(0).s.hidden != -1 || w.at(1).s.shown != -1) { return 6; }
    tb: Vec<u8> = encodeValue(Tok.Pair(r, w.cloneAt(1)));
    tv: [u8] = "";
    unsafe { tv = bytesOf(&tb); }
    tok: Result<Tok, str> = decodeValue(tv);
    if (!tok.isOk()) { return 7; }
    if (nameof(Tok, tok.unwrap()) != "Pair") { return 8; }
    return 0;
}
