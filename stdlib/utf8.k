// UTF-8: code points out of bytes and back.
//
//     cps: Vec<long> = decodeUtf8(bytes);       // bad bytes become U+FFFD, as browsers do
//     s.pushCodePoint(0x1F525);                 // the four bytes of U+1F525
//     n: long = utf8Len(cp);                    // how many bytes a code point takes
//     at: Utf8At = utf8At(bytes, i);            // one code point and its length, at byte i
//
// Decoding is the WHATWG Encoding standard's UTF-8 decoder, which is what Python's
// `errors="replace"` does too: each maximal invalid subpart of a sequence becomes one U+FFFD,
// and the bytes after it are read afresh. Overlong forms, surrogates (U+D800..U+DFFF) and
// anything past U+10FFFF are invalid. `decodeWtf8` is the one exception: it lets an encoded
// surrogate through as itself, which is the form a JavaScript string or a test suite's lone
// surrogate takes when it has to travel as bytes (WTF-8).
#include <{core, vec, string}>

pub REPLACEMENT_CHAR: long = 0xFFFD;

// A code point and how many bytes it took.
pub struct Utf8At { cp: long, len: long }

// The code point starting at byte `i` of `b` (i < b.len).
pub utf8At b:[u8] i:long -> Utf8At { return decodeOne(b, i, false); }

pub decodeUtf8 b:[u8] -> Vec<long> { return decodeWith(b, false); }
pub decodeWtf8 b:[u8] -> Vec<long> { return decodeWith(b, true); }

local decodeWith b:[u8] surrogates:bool -> Vec<long> {
    out: Vec<long>;
    out.reserve(b.len);
    i: long = 0;
    while (i < b.len) {
        c: long = b[i];
        if (c < 0x80) { out.push(c); i = i + 1; continue; }      // the common case, inline
        at: Utf8At = decodeOne(b, i, surrogates);
        out.push(at.cp);
        i += at.len;
    }
    return out;
}

// The decoder's one step. `need` continuation bytes follow a lead byte, and the first of them
// has a narrower range for the leads where the full range would allow an overlong form, a
// surrogate or a value past U+10FFFF (E0, ED, F0, F4).
local decodeOne b:[u8] i:long surrogates:bool -> Utf8At {
    c: long = b[i];
    if (c < 0x80) { return Utf8At { cp: c, len: 1 }; }
    need: long = 0;
    cp: long = 0;
    lo: long = 0x80;
    hi: long = 0xBF;
    if (c >= 0xC2 && c <= 0xDF) { need = 1; cp = c & 0x1F; }
    else if (c >= 0xE0 && c <= 0xEF) {
        need = 2;
        cp = c & 0xF;
        if (c == 0xE0) { lo = 0xA0; }
        if (c == 0xED && !surrogates) { hi = 0x9F; }
    }
    else if (c >= 0xF0 && c <= 0xF4) {
        need = 3;
        cp = c & 0x7;
        if (c == 0xF0) { lo = 0x90; }
        if (c == 0xF4) { hi = 0x8F; }
    }
    else { return Utf8At { cp: REPLACEMENT_CHAR, len: 1 }; }      // a stray continuation, C0, C1, F5..FF
    j: long = 1;
    while (j <= need) {
        if (i + j >= b.len) { return Utf8At { cp: REPLACEMENT_CHAR, len: j }; }   // cut short at the end
        d: long = b[i + j];
        if (d < lo || d > hi) { return Utf8At { cp: REPLACEMENT_CHAR, len: j }; } // d is read again
        lo = 0x80;
        hi = 0xBF;
        cp = (cp << 6) | (d & 0x3F);
        j += 1;
    }
    return Utf8At { cp: cp, len: need + 1 };
}

// Bytes a code point takes; a surrogate counts its WTF-8 three.
pub utf8Len cp:long -> long {
    if (cp < 0x80) { return 1; }
    if (cp < 0x800) { return 2; }
    if (cp < 0x10000) { return 3; }
    return 4;
}

// Write `cp` as UTF-8 into `out` (at most 4 bytes); answers how many. A surrogate is written as
// its three WTF-8 bytes, and anything outside 0..=0x10FFFF as U+FFFD.
pub encodeUtf8 cp:long inout out:[u8] -> long {
    v: long = cp;
    if (v < 0 || v > 0x10FFFF) { v = REPLACEMENT_CHAR; }
    if (v < 0x80) { out[0] = v as u8; return 1; }
    if (v < 0x800) {
        out[0] = (0xC0 | (v >> 6)) as u8;
        out[1] = (0x80 | (v & 0x3F)) as u8;
        return 2;
    }
    if (v < 0x10000) {
        out[0] = (0xE0 | (v >> 12)) as u8;
        out[1] = (0x80 | ((v >> 6) & 0x3F)) as u8;
        out[2] = (0x80 | (v & 0x3F)) as u8;
        return 3;
    }
    out[0] = (0xF0 | (v >> 18)) as u8;
    out[1] = (0x80 | ((v >> 12) & 0x3F)) as u8;
    out[2] = (0x80 | ((v >> 6) & 0x3F)) as u8;
    out[3] = (0x80 | (v & 0x3F)) as u8;
    return 4;
}

methods String {
    // Append one code point as UTF-8 (a surrogate as WTF-8; out of range as U+FFFD).
    pushCodePoint &self cp:long -> void {
        if (cp >= 0 && cp < 0x80) { self.push(cp as char); return; }
        b: [u8; 4];
        n: long = encodeUtf8(cp, &b[..]);
        unsafe { self.pushStr(b[..n] as str); }
    }
}
