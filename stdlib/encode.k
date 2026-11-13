// `Encode` and `Decode`: values to bytes and back, for any type.
//
// Every type gets an implementation without anyone writing one: both traits name a derive macro
// (`trait Encode derive deriveEncode`), and the first time a program needs `T: Encode` for a T
// with no `methods T for Encode`, the compiler runs `deriveEncode` on T's declaration and
// compiles what it writes. A hand-written implementation always wins. The macros are ordinary
// library code at the bottom of this file; nothing in the compiler knows these two traits.
//
//     #include <stdlib::encode>
//     struct Point { x: long, y: long }
//     e: Encoder;
//     p.encode(e);                          // Point: Encode, derived the first time it is needed
//     bytes: Vec<u8> = e.bytes();
//     view: [u8] = "";
//     unsafe { view = bytesOf(&bytes); }    // a view of the vector, as `String.view` is
//     d: Decoder = decoderOf(view);
//     q: Point = Point.decode(d);           // and Point: Decode
//     if (!d.done()) { ...d.error()... }
//
//     b: Vec<u8> = encodeValue(p);          // the same in one call each way, the type of the
//     r: Result<Point, str> = decodeValue(view);  // decode taken from where it is stored
//
// ─── the format ──────────────────────────────────────────────────────────────
// Compact and unframed: nothing says what a value is, so the reader must know its type.
//
//   bool, u8, char          one byte (a bool is 0 or 1; anything else is refused)
//   i16, int, long          zigzag LEB128: n -> (n << 1) ^ (n >> 63), seven bits a byte, low
//                           first, the high bit set on every byte but the last (-1 is one byte)
//   u16, u32, u64           LEB128, the same without the zigzag
//   str, String             the byte length (LEB128), then the bytes
//   Vec<T>                  the length (LEB128), then each element
//   HashMap<K, V>           the entry count (LEB128), then key, value, key, value... in slot order
//   Box<T>                  the T
//   a struct (derived)      each field, in declaration order; nothing between them
//   a sum type (derived)    the variant's tag (LEB128), then its payloads in order -- so
//                           `Option<T>` is 0, or 1 and the T, and `Result<T, E>` likewise
//   a backed enum (derived) its integer, zigzag LEB128 (`enum Color: int { ... }`)
//
// ─── failure ─────────────────────────────────────────────────────────────────
// Decoding never traps and never reads past its input. The first problem -- the input ends, a
// length is longer than what is left, a bool is 2, a tag names no variant, a value does not fit
// its type -- puts the `Decoder` in a failed state that keeps its first reason; every read after
// it answers zero (or empty) at once, so a decode written as straight-line code needs no check
// per field and ends quickly. Check `ok()` (or `done()`, which also wants the input used up)
// once, at the end. `decodeValue` does all of that and hands back a `Result`.
//
// Efficiency: an encoder appends to one growable buffer, reserving before every multi-byte
// write; bytes and strings are one `memcpy`; decoding a `str` is a VIEW into the input (no copy:
// it lives as long as the input does), a `String` one allocation of exactly its length, and a
// `Vec` reserves its decoded length once. Raw bytes go through `putBytes`/`getBytes` (a length,
// then one copy); a `Vec<u8>` encodes the same bytes but element by element, since nothing lets
// `Vec<T>`'s implementation specialize for u8. A length longer than the bytes left is refused
// before anything is allocated, which is what makes a hostile length harmless (and a `Vec` of an
// empty struct, whose elements encode to nothing, undecodable past length 0).
//
// Not covered: floats, inline arrays, raw and function pointers, trait objects. The derive refuses
// the last four by name. (Tuples are covered by the derives themselves.)
#include <{core, vec, mem, heap, string, map, option, result, panic, fmt, ast, reflect, float}>

// ─── Encoder ─────────────────────────────────────────────────────────────────

pub struct Encoder { out: Vec<u8> }

methods Encoder for Default {
    new -> Encoder { v: Vec<u8>; return Encoder { out: v }; }
}

methods Encoder {
    len &self -> long { return self.out.len(); }
    // Room for `n` more bytes, for a caller that knows how much it is about to write.
    reserve &self n:long -> void { self.out.reserve(n); }

    putU8 &self b:u8 -> void { self.out.push(b); }
    // LEB128: seven bits a byte, low first, the high bit on every byte but the last.
    putUvarint &self v:u64 -> void {
        self.out.reserve(10);
        n: long = self.out.count;
        unsafe {
            p: *u8 = self.out.buf.ptr;
            while ((v >> 7) != 0) {
                p[n] = ((v & 127) | 128) as u8;
                v = v >> 7;
                n = n + 1;
            }
            p[n] = v as u8;
        }
        self.out.count = n + 1;
    }
    // Zigzag first, so a small negative number is as short as a small positive one.
    putVarint &self v:long -> void { self.putUvarint(((v << 1) ^ (v >> 63)) as u64); }
    // Fixed width, low byte first: what a float's bits are written as.
    putU64LE &self v:u64 -> void {
        b: [u8; 8];
        for k in 0..8 { b[k] = ((v >> (k * 8)) & 255) as u8; }
        self.putRaw(b[..]);
    }
    putU32LE &self v:u32 -> void {
        b: [u8; 4];
        for k in 0..4 { b[k] = ((v >> (k * 8)) & 255) as u8; }
        self.putRaw(b[..]);
    }
    // Bytes as they are, in one copy.
    putRaw &self b:[u8] -> void {
        if (b.len == 0) { return; }
        self.out.reserve(b.len);
        unsafe { memcpy((self.out.buf.ptr + self.out.count) as long, b.ptr as long, b.len); }
        self.out.count = self.out.count + b.len;
    }
    putLen &self n:long -> void { self.putUvarint(n as u64); }
    // A length, then the bytes.
    putBytes &self b:[u8] -> void { self.putLen(b.len); self.putRaw(b); }
    putStr &self s:str -> void { self.putLen(s.len); self.putRaw(s as [u8]); }

    // The bytes written, handed over; the encoder is consumed.
    bytes self -> Vec<u8> { return self.out; }
    // The bytes written so far, in place. `unsafe` as `String.view` is: writing again may move
    // them, and dropping the encoder frees them.
    unsafe view &self -> [u8] { return self.out.buf.ptr[..self.out.count]; }
}

// A `Vec<u8>`'s bytes, in place: what a `Decoder` reads an encoder's output from. `unsafe`
// for the same reason: the view dies with the vector, or when it grows.
pub unsafe bytesOf v:&Vec<u8> -> [u8] { return v.buf.ptr[..v.count]; }

// ─── Decoder ─────────────────────────────────────────────────────────────────

// The input is held as its address and length (a struct cannot hold a slice), and every read is
// bounds-checked here: the decoder never reads outside it.
pub struct Decoder { at: *u8, len: long, pos: long, failed: bool, why: str }

// The two traits. Each names the macro that writes its implementation for a type nobody wrote
// one for (see the derives at the end of this file).
pub trait Encode derive deriveEncode { encode &self out:&Encoder -> void; }
pub trait Decode derive deriveDecode { decode inp:&Decoder -> Self; }

// A decoder reading `data` from its start. It holds a view: `data` must outlive it, and so must
// every `str` it decodes, since those are views into `data` too.
pub decoderOf data:[u8] -> Decoder {
    unsafe { return Decoder { at: data.ptr, len: data.len, pos: 0, failed: false, why: "" }; }
}

methods Decoder {
    ok &self -> bool { return !self.failed; }
    // Nothing went wrong, and every byte was read.
    done &self -> bool { return !self.failed && self.pos == self.len; }
    // Why the decode failed: the first problem met, or "" if none was.
    error &self -> str { return self.why; }
    remaining &self -> long { return self.len - self.pos; }

    // The first failure is the one kept. Every read after it answers zero at once.
    fail &self why:str -> void {
        if (!self.failed) { self.failed = true; self.why = why; }
        self.pos = self.len;
    }

    getU8 &self -> u8 {
        if (self.pos >= self.len) { self.fail("the input ends inside a value"); return 0; }
        b: u8 = 0;
        unsafe { b = self.at[self.pos]; }
        self.pos = self.pos + 1;
        return b;
    }
    getUvarint &self -> u64 {
        v: u64 = 0;
        shift: long = 0;
        while (shift < 64) {
            if (self.pos >= self.len) { self.fail("the input ends inside a value"); return 0; }
            b: long = 0;
            unsafe { b = self.at[self.pos] as long; }
            self.pos = self.pos + 1;
            v = v | (((b & 127) as u64) << shift);
            if (b < 128) {
                // The tenth byte may carry only the 64th bit.
                if (shift == 63 && b > 1) { self.fail("a number wider than 64 bits"); return 0; }
                return v;
            }
            shift = shift + 7;
        }
        self.fail("a number wider than 64 bits");
        return 0;
    }
    getU64LE &self -> u64 {
        b: [u8] = self.getRaw(8);
        v: u64 = 0;
        for k in 0..b.len { v = v | ((b[k] as u64) << (k * 8)); }
        return v;
    }
    getU32LE &self -> u32 {
        b: [u8] = self.getRaw(4);
        v: u32 = 0;
        for k in 0..b.len { v = v | ((b[k] as u32) << (k * 8)); }
        return v;
    }
    getVarint &self -> long {
        u: u64 = self.getUvarint();
        return ((u >> 1) as long) ^ (0 - ((u & 1) as long));
    }
    // A count of things still to read, each at least one byte: one larger than what is left is
    // refused here, before anything is allocated for it.
    getLen &self -> long {
        u: u64 = self.getUvarint();
        n: long = u as long;
        if (n < 0 || n > self.len - self.pos) { self.fail("a length longer than the input left"); return 0; }
        return n;
    }
    // A sum type's tag: any number, checked by the caller against its variants.
    getTag &self -> long { return self.getUvarint() as long; }
    // The next `n` bytes, in place.
    getRaw &self n:long -> [u8] {
        if (n < 0 || n > self.len - self.pos) { self.fail("a length longer than the input left"); n = 0; }
        at: long = self.pos;
        self.pos = self.pos + n;
        unsafe { return (self.at + at)[..n]; }
    }
    getBytes &self -> [u8] { return self.getRaw(self.getLen()); }
    getStr &self -> str { return self.getBytes() as str; }
}

// The bytes `v` encodes to.
pub encodeValue<T: Encode> v:T -> Vec<u8> {
    e: Encoder;
    v.encode(e);
    return e.bytes();
}
// A `T` decoded from all of `data`, or why not: a failed read, or bytes left over after it.
// `T` comes from where the result is stored: `r: Result<Point, str> = decodeValue(bytes)`.
pub decodeValue<T: Decode> data:[u8] -> Result<T, str> {
    d: Decoder = decoderOf(data);
    v: T = T.decode(d);
    if (!d.ok()) { return Result.Err(d.error()); }
    if (d.remaining() > 0) { return Result.Err("bytes left over after the value"); }
    return Result.Ok(v);
}

// ─── the scalars, strings and containers, by hand ────────────────────────────

methods bool for Encode { encode &self out:&Encoder -> void { if (self) { out.putU8(1); } else { out.putU8(0); } } }
methods bool for Decode {
    decode inp:&Decoder -> bool {
        b: u8 = inp.getU8();
        if (b > 1) { inp.fail("a bool that is neither 0 nor 1"); }
        return b == 1;
    }
}
methods u8 for Encode { encode &self out:&Encoder -> void { out.putU8(self); } }
methods u8 for Decode { decode inp:&Decoder -> u8 { return inp.getU8(); } }
methods char for Encode { encode &self out:&Encoder -> void { out.putU8(self as u8); } }
methods char for Decode { decode inp:&Decoder -> char { return inp.getU8() as char; } }

methods long for Encode { encode &self out:&Encoder -> void { out.putVarint(self); } }
methods long for Decode { decode inp:&Decoder -> long { return inp.getVarint(); } }
methods int for Encode { encode &self out:&Encoder -> void { out.putVarint(self as long); } }
methods int for Decode {
    decode inp:&Decoder -> int {
        v: long = inp.getVarint();
        if (v < -2147483648 || v > 2147483647) { inp.fail("a number too wide for an int"); return 0; }
        return v as int;
    }
}
methods i16 for Encode { encode &self out:&Encoder -> void { out.putVarint(self as long); } }
methods i16 for Decode {
    decode inp:&Decoder -> i16 {
        v: long = inp.getVarint();
        if (v < -32768 || v > 32767) { inp.fail("a number too wide for an i16"); return 0; }
        return v as i16;
    }
}
methods u64 for Encode { encode &self out:&Encoder -> void { out.putUvarint(self); } }
methods u64 for Decode { decode inp:&Decoder -> u64 { return inp.getUvarint(); } }
methods u32 for Encode { encode &self out:&Encoder -> void { out.putUvarint(self as u64); } }
methods u32 for Decode {
    decode inp:&Decoder -> u32 {
        v: u64 = inp.getUvarint();
        if ((v >> 32) != 0) { inp.fail("a number too wide for a u32"); return 0; }
        return v as u32;
    }
}
methods u16 for Encode { encode &self out:&Encoder -> void { out.putUvarint(self as u64); } }
methods u16 for Decode {
    decode inp:&Decoder -> u16 {
        v: u64 = inp.getUvarint();
        if ((v >> 16) != 0) { inp.fail("a number too wide for a u16"); return 0; }
        return v as u16;
    }
}

// A `str` decodes to a view into the decoder's input: no copy, and it lives as long as that.
methods f64 for Encode { encode &self out:&Encoder -> void { out.putU64LE(self.toBits()); } }
methods f64 for Decode { decode inp:&Decoder -> f64 { return f64.fromBits(inp.getU64LE()); } }
methods f32 for Encode { encode &self out:&Encoder -> void { out.putU32LE(self.toBits()); } }
methods f32 for Decode { decode inp:&Decoder -> f32 { return f32.fromBits(inp.getU32LE()); } }
methods str for Encode { encode &self out:&Encoder -> void { out.putStr(self); } }
methods str for Decode { decode inp:&Decoder -> str { return inp.getStr(); } }
methods String for Encode { encode &self out:&Encoder -> void { unsafe { out.putStr(self.view()); } } }
methods String for Decode { decode inp:&Decoder -> String { return stringOf(inp.getStr()); } }

methods Vec<T: Encode> for Encode {
    encode &self out:&Encoder -> void {
        out.putLen(self.len());
        for x in self { x.encode(out); }
    }
}
methods Vec<T: Decode> for Decode {
    decode inp:&Decoder -> Vec<T> {
        n: long = inp.getLen();
        v: Vec<T>;
        v.reserve(n);
        for i in 0..n { v.push(T.decode(inp)); }
        return v;
    }
}

methods Box<T: Encode> for Encode { encode &self out:&Encoder -> void { self.at().encode(out); } }
methods Box<T: Decode> for Decode { decode inp:&Decoder -> Box<T> { return newBox(T.decode(inp)); } }

methods HashMap<K: Encode, V: Encode> for Encode {
    encode &self out:&Encoder -> void {
        out.putLen(self.len());
        i: long = self.nextSlot(-1);
        while (i >= 0) {
            self.keyAt(i).encode(out);
            self.valAt(i).encode(out);
            i = self.nextSlot(i);
        }
    }
}
methods HashMap<K: Decode, V: Decode> for Decode {
    decode inp:&Decoder -> HashMap<K, V> {
        n: long = inp.getLen();
        m: HashMap<K, V>;
        m.reserve(n);
        for i in 0..n {
            k: K = K.decode(inp);
            v: V = V.decode(inp);
            m.put(k, v);
        }
        return m;
    }
}

// ─── the derives ─────────────────────────────────────────────────────────────
// Each is handed the type's declaration (`stdlib::reflect`) and writes the methods block. A
// struct: each field in order. A sum type: the tag, then the live variant's payloads, read in
// place (`self.$V$k`, the slot the compiler lays a payload in), so nothing is moved out of the
// value being encoded. A backed enum: its integer.

pub macro deriveEncode d:Decl -> Node {
    r: Node = Node.Nothing;
    match d {
        OfStruct(t) { r = encodeOfStruct(t); }
        OfEnum(e)   { r = encodeOfEnum(e); }
    }
    return r;
}

pub macro deriveDecode d:Decl -> Node {
    r: Node = Node.Nothing;
    match d {
        OfStruct(t) { r = decodeOfStruct(t); }
        OfEnum(e)   { r = decodeOfEnum(e); }
    }
    return r;
}

// What a value of this field's type cannot be written as.
local encodableField owner:str f:Field -> void {
    why: str = "";
    if (f.isRawPointer)       { why = " is a raw pointer, an address that means nothing outside this process"; }
    else if (f.isFn)          { why = " is a function pointer, an address that means nothing outside this process"; }
    else if (f.isTraitObject) { why = " is a trait object, whose concrete type a decoder could not know"; }
    else if (f.isArray)       { why = " is an inline array, which is not supported yet"; }
    if (why.len > 0) { refuse(format("{}.{}{}", owner, f.name, why)); }
}

local encodeOfStruct t:Struct -> Node {
    stmts: Vec<Node>;
    stmts.reserve(t.fields.len());
    for f in t.fields {
        encodableField(t.name, f);
        stmts.push(quote { self.@(f.name).encode(out); });
    }
    return quote { methods @(t.name) for Encode { encode &self out:&Encoder -> void { @stmts } } };
}

local decodeOfStruct t:Struct -> Node {
    names: Vec<str>;
    vals: Vec<Node>;
    for f in t.fields {
        encodableField(t.name, f);
        names.push(f.name);
        vals.push(quote { @(Node.Name(f.typeName)).decode(inp) });
    }
    built: Node = Node.StructLit(t.name, names, vals);
    return quote { methods @(t.name) for Decode { decode inp:&Decoder -> Self { return @built; } } };
}

local encodeOfEnum e:Enum -> Node {
    if (e.isBacked) {
        return quote { methods @(e.name) for Encode { encode &self out:&Encoder -> void { out.putVarint(self as long); } } };
    }
    arms: Vec<Node>;
    for v in e.variants {
        if (v.payloads.len() == 0) { continue; }
        ps: Vec<Node>;
        for j in 0..v.payloads.len() {
            p: Field = v.payloads.get(j);
            encodableField(e.name, p);
            ps.push(quote { self.@(p.name).encode(out); });
        }
        which: Node = Node.Int(v.tag);
        arms.push(quote { if (tag == @which) { @ps } });
    }
    return quote { methods @(e.name) for Encode {
        encode &self out:&Encoder -> void {
            tag: long = self.@(e.tagField) as long;
            out.putUvarint(tag as u64);
            @arms
        }
    } };
}

// A variant built from the decoder: each payload decoded in order.
local decodedVariant e:Enum v:Variant -> Node {
    args: Vec<Node>;
    for p in v.payloads {
        encodableField(e.name, p);
        args.push(quote { @(Node.Name(p.typeName)).decode(inp) });
    }
    return Node.VariantLit(e.name, v.name, args);
}

local decodeOfEnum e:Enum -> Node {
    if (e.isBacked) {
        // An enum with no variants (`enum Sym: long { }`, a typed integer) takes any value; one
        // with variants only theirs, and a stray one fails the decode and reads as the first.
        if (e.variants.len() == 0) {
            return quote { methods @(e.name) for Decode { decode inp:&Decoder -> Self { return inp.getVarint() as @(e.name); } } };
        }
        known: Node = Node.Nothing;
        for i in 0..e.variants.len() {
            one: Node = Node.Binary(BinOp.Eq, newBox(Node.Name("v")), newBox(Node.Int(e.variants.at(i).tag)));
            if (i == 0) { known = one; }
            else { known = Node.Binary(BinOp.Or, newBox(known), newBox(one)); }
        }
        first: Node = Node.Int(e.variants.at(0).tag);
        return quote { methods @(e.name) for Decode {
            decode inp:&Decoder -> Self {
                v: long = inp.getVarint();
                if (!(@known)) { inp.fail("a value the enum has no variant for"); v = @first; }
                return v as @(e.name);
            }
        } };
    }
    if (e.variants.len() == 0) { refuse(format("{} has no variants, so no value of it can be decoded", e.name)); }
    arms: Vec<Node>;
    fallback: long = 0;
    for i in 0..e.variants.len() {
        if (e.variants.at(i).payloads.len() < e.variants.at(fallback).payloads.len()) { fallback = i; }
        which: Node = Node.Int(e.variants.at(i).tag);
        built: Node = decodedVariant(e, e.variants.at(i));
        arms.push(quote { if (tag == @which) { return @built; } });
    }
    // A tag no variant has: the decode fails, and the value is the variant with the fewest
    // payloads, read from a decoder that now answers zero to everything.
    other: Node = decodedVariant(e, e.variants.at(fallback));
    return quote { methods @(e.name) for Decode {
        decode inp:&Decoder -> Self {
            tag: long = inp.getTag();
            @arms
            inp.fail("a tag no variant has");
            return @other;
        }
    } };
}
