// Strings you can build, compare and take apart.
//
// A `str` is a borrowed {ptr, len} view over bytes somebody else owns; `String` owns its bytes
// and grows. `String.view` is `unsafe` because the view it hands out points into the buffer and
// dangles if the String is dropped or grown while it is held. Little needs it: printing goes
// through `Display`, appending through `Write`, and the search and comparison methods below take
// a `str` argument and read the buffer internally. (A method cannot hand out the text as a
// call-scoped borrow, `-> &str`, the way `Vec.at` hands out an element — see STDLIB_REVIEW.md —
// so the views are taken inside this file and nowhere else has to.)
//
//     s: String;                       // Default: empty, no allocation
//     s.pushStr("total: ");
//     writeTo(s, "{}", 42);            // a String is a Write sink, so formatting appends
//     println("{}", s);                //  -> total: 42
#include <{core, cmp, heap, mem, bytes, fmt, option, chars, vec}>

// ─── str readers ─────────────────────────────────────────────────────────────
// Free functions, kept as the names they have always had; the trait implementations below
// answer to the same three. All are safe: a sub-view of a `str` the caller already holds
// lives exactly as long as it does.

// Same TEXT.
pub strEq a:str b:str -> bool { return bytesEqual(a as [u8], b as [u8]); }

// Lexicographic by bytes, then by length. Negative / zero / positive.
pub strCmp a:str b:str -> int { return bytesCompare(a as [u8], b as [u8]); }

// FNV-1a over the CONTENTS — what a str-keyed table needs. Hashing the header would hash the
// address, so two equal strings in different places would never match.
pub strHash s:str -> long { return hashBytes(s as [u8]); }

// A `str` compares, orders and hashes BY ITS CONTENT. Nothing else would be defensible: two
// equal strings at different addresses are equal, and a table that disagreed would lose them.
// These are what make `a == b`, `sort(&v)` and `HashMap<str, V>` mean what they read as.
methods str for Eq<str> { eq  &self other:str -> bool { return strEq(self, other); } }
methods str for Ord     { cmp &self other:str -> int  { return strCmp(self, other); } }
methods str for Hash    { hash &self -> u64 { return strHash(self) as u64; } }

pub strStartsWith s:str prefix:str -> bool {
    if (prefix.len > s.len) { return false; }
    return bytesEqual((s as [u8])[..prefix.len], prefix as [u8]);
}
pub strEndsWith s:str suffix:str -> bool {
    if (suffix.len > s.len) { return false; }
    return bytesEqual((s as [u8])[s.len - suffix.len..], suffix as [u8]);
}

// Byte index of the first occurrence at or after `from`, or nothing. Finds the needle's first
// byte with a plain scan and compares the rest only there: the needles this is for are short,
// and Boyer-Moore's preprocessing pass only pays back on long ones.
pub strFindFrom s:str needle:str from:long -> Option<long> {
    start: long = from;
    if (start < 0) { start = 0; }
    if (needle.len == 0) {
        if (start > s.len) { return Option.None; }
        return Option.Some(start);
    }
    hay: [u8] = s as [u8];
    pat: [u8] = needle as [u8];
    last: long = s.len - needle.len;
    i: long = bytesIndexOf(hay, pat[0], start);
    while (i >= 0 && i <= last) {
        if (bytesEqual(hay[i..i + pat.len], pat)) { return Option.Some(i); }
        i = bytesIndexOf(hay, pat[0], i + 1);
    }
    return Option.None;
}
pub strFind s:str needle:str -> Option<long> { return strFindFrom(s, needle, 0); }

pub strFindLast s:str needle:str -> Option<long> {
    if (needle.len > s.len) { return Option.None; }
    hay: [u8] = s as [u8];
    pat: [u8] = needle as [u8];
    i: long = s.len - needle.len;
    while (i >= 0) {
        if (bytesEqual(hay[i..i + pat.len], pat)) { return Option.Some(i); }
        i = i - 1;
    }
    return Option.None;
}
pub strContains s:str needle:str -> bool {
    f: Option<long> = strFind(s, needle);
    return f.isSome();
}
// How many times `needle` occurs, not overlapping. An empty needle occurs nowhere.
pub strCount s:str needle:str -> long {
    if (needle.len == 0) { return 0; }
    n: long = 0;
    at: long = 0;
    loop {
        f: Option<long> = strFindFrom(s, needle, at);
        match f {
            Some(i) { n = n + 1; at = i + needle.len; }
            None    { return n; }
        }
    }
}

// ─── trimming ────────────────────────────────────────────────────────────────
// What counts as the edge is a choice: whitespace (ASCII space and the usual control
// whitespace) by default, or any byte of a set the caller names.

local inSet c:long set:str -> bool { return bytesIndexOf(set as [u8], c as u8, 0) >= 0; }

pub strTrimStart s:str -> str {
    a: long = 0;
    while (isSpace(charAt(s, a))) { a = a + 1; }
    return strSlice(s, a, s.len - a);
}
pub strTrimEnd s:str -> str {
    b: long = s.len;
    while (b > 0 && isSpace(charAt(s, b - 1))) { b = b - 1; }
    return strSlice(s, 0, b);
}
pub strTrim s:str -> str { return strTrimEnd(strTrimStart(s)); }

// Both ends, minus every byte that appears in `set`: `strTrimSet("--x--", "-")` is "x".
pub strTrimSet s:str set:str -> str {
    a: long = 0;
    b: long = s.len;
    while (a < b && inSet(charAt(s, a), set))     { a = a + 1; }
    while (b > a && inSet(charAt(s, b - 1), set)) { b = b - 1; }
    return strSlice(s, a, b - a);
}

// ─── splitting ───────────────────────────────────────────────────────────────
// The pieces are views INTO `s`, so nothing is copied and every one dies when `s` does.

// Split on a single byte, keeping empty pieces: `strSplit("a,,b", ',')` is three.
pub strSplit s:str sep:long -> Vec<str> {
    out: Vec<str>;
    start: long = 0;
    for i in 0..s.len {
        if (charAt(s, i) == sep) {
            out.push(strSlice(s, start, i - start));
            start = i + 1;
        }
    }
    out.push(strSlice(s, start, s.len - start));
    return out;
}

// Split on a separator of any length, keeping empty pieces: `strSplitOn("a::b", "::")` is two.
// An empty separator does not split.
pub strSplitOn s:str sep:str -> Vec<str> {
    out: Vec<str>;
    if (sep.len == 0) { out.push(s); return out; }
    start: long = 0;
    loop {
        f: Option<long> = strFindFrom(s, sep, start);
        match f {
            Some(i) { out.push(strSlice(s, start, i - start)); start = i + sep.len; }
            None    { out.push(strSlice(s, start, s.len - start)); return out; }
        }
    }
}

// Every line, without its terminator. Unlike `strSplit`, a trailing newline does NOT produce a
// final empty line — a file's line count is then what an editor would show. A CR before the
// newline is left on the line, so a tool that writes its input back out does not silently
// convert CRLF to LF.
pub splitLines body:str -> Vec<str> {
    out: Vec<str> = strSplit(body, '\n');
    last: str = out.last();
    if (last.len == 0) { out.pop(); }        // the trailing newline's empty tail, or "" itself
    return out;
}

// ─── parsing ─────────────────────────────────────────────────────────────────

// An optional sign then digits of `base` (2..36; letters either case), and nothing else — no
// whitespace skipping, no `0x`, and no partial parse that reports success for a prefix.
// Refuses rather than wraps: a value outside `long` is nothing.
pub parseLongBase s:str base:long -> Option<long> {
    i: long = 0;
    neg: bool = false;
    c0: long = charAt(s, 0);
    if (c0 == '-' || c0 == '+') { neg = c0 == '-'; i = 1; }
    if (i >= s.len || base < 2 || base > 36) { return Option.None; }   // empty, or a sign alone
    // Accumulate NEGATIVELY: the negative range is one larger, so long's minimum parses too.
    limit: long = -9223372036854775807 - 1;
    v: long = 0;
    while (i < s.len) {
        d: long = digitVal(charAt(s, i), base);
        if (d < 0) { return Option.None; }
        if (v < (limit + d) / base) { return Option.None; }   // v * base - d would pass the limit
        v = v * base - d;
        i = i + 1;
    }
    if (neg) { return Option.Some(v); }
    if (v == limit) { return Option.None; }                   // 2^63 has no positive twin
    return Option.Some(-v);
}
pub parseLong s:str -> Option<long> { return parseLongBase(s, 10); }

// ─── String: bytes you own ───────────────────────────────────────────────────
pub struct String { buf: *u8, len: long, cap: long }

methods String for Default {
    // A String that is never written to never calls the allocator.
    new -> String { unsafe { return String { buf: 0 as *u8, len: 0, cap: 0 }; } }
}

methods String for Drop {
    drop &self -> void { if (self.cap > 0) { unsafe { free(self.buf as long); } } }
}

methods String for Clone {
    clone &self -> String {
        out: String;
        out.pushString(self);
        return out;
    }
}

// Appending is writing, so a String is a sink: `writeTo(s, "{} of {}", a, b)` appends formatted
// text, and every number-to-text conversion in fmt.k comes along with it.
methods String for Write {
    write &self ptr:long len:long -> long {
        if (len <= 0) { return 0; }
        self.reserve(len);
        unsafe { memcpy(self.buf as long + self.len, ptr, len); }
        self.len = self.len + len;
        return len;
    }
}

methods String for Display {
    display &self w:Write -> void {
        if (self.len > 0) { unsafe { w.write(self.buf as long, self.len); } }
    }
}

methods String {
    length  &self -> long { return self.len; }
    isEmpty &self -> bool { return self.len == 0; }
    capacity &self -> long { return self.cap; }

    // Room for `extra` more bytes. Capacity doubles rather than growing by what was asked, so a
    // string built one push at a time costs amortized O(1) per byte. Growing goes through realloc,
    // which keeps the block when it has room and moves a large one's pages rather than copying.
    reserve &self extra:long -> void {
        need: long = self.len + extra;
        if (need <= self.cap) { return; }
        n: long = self.cap;
        if (n == 0) { n = 16; }
        while (n < need) { n = n * 2; }
        unsafe {
            if (self.cap > 0) { self.buf = realloc(self.buf as long, self.len, n) as *u8; }
            else { self.buf = malloc(n) as *u8; }
            self.cap = n;
        }
    }

    // Forget the contents, keep the buffer, so a scratch String in a loop allocates once.
    clear &self -> void { self.len = 0; }
    // Keep the first `n` bytes (all of them, if there are fewer).
    truncate &self n:long -> void { if (n >= 0 && n < self.len) { self.len = n; } }

    push &self c:char -> void {
        self.reserve(1);
        unsafe { self.buf[self.len] = c as u8; }
        self.len = self.len + 1;
    }
    // `c`, `n` times: padding, rules, indentation.
    pushRepeated &self c:char n:long -> void {
        if (n <= 0) { return; }
        self.reserve(n);
        unsafe { memset(self.buf as long + self.len, c as long, n); }
        self.len = self.len + n;
    }
    pushStr &self s:str -> void {
        if (s.len > 0) { unsafe { self.write(s.ptr, s.len); } }
    }
    // `other` is only read, so it is borrowed. Written out rather than left to
    // `a.pushStr(b.view())`, which would make an append that needs no borrow to escape demand
    // `unsafe` at the call site.
    pushString &self other:String -> void {
        if (other.len > 0) { unsafe { self.write(other.buf as long, other.len); } }
    }
    // A number appended in decimal, without going through the formatter's spec parsing. `{}`
    // through `writeTo` is the general way; this is the one a builder assembling text in a loop
    // wants, and it is also what an `inout String` parameter can call — a borrow does not
    // convert to the `Write` trait object `putLong` takes.
    pushLong &self v:long -> void {
        scratch: [u8; LONG_TEXT_MAX];
        n: long = fmtDec(v, &scratch[..]);
        self.pushStr(scratch[..n] as str);
    }
    pushULong &self v:u64 -> void {
        scratch: [u8; LONG_TEXT_MAX];
        n: long = fmtDecMagU(v, &scratch[..]);
        self.pushStr(scratch[..n] as str);
    }

    // The last byte, removed; nothing if the String is empty.
    pop &self -> Option<char> {
        if (self.len == 0) { return Option.None; }
        self.len = self.len - 1;
        unsafe { return Option.Some(self.buf[self.len] as char); }
    }

    // ASCII case, in place.
    makeUpper &self -> void { unsafe { for i in 0..self.len { self.buf[i] = toUpper(self.buf[i]) as u8; } } }
    makeLower &self -> void { unsafe { for i in 0..self.len { self.buf[i] = toLower(self.buf[i]) as u8; } } }

    // The text as a borrowed view. `unsafe` because it points INTO this String: dropping it or
    // growing it (any push, any write) leaves the view on freed or stale bytes.
    unsafe view &self -> str { return self.buf[..self.len] as str; }

    // Search and prefix tests without exposing the buffer — the reason `view` is rarely needed.
    startsWith &self prefix:str -> bool { unsafe { return strStartsWith(self.view(), prefix); } }
    endsWith   &self suffix:str -> bool { unsafe { return strEndsWith(self.view(), suffix); } }
    contains   &self needle:str -> bool { unsafe { return strContains(self.view(), needle); } }
    find       &self needle:str -> Option<long> { unsafe { return strFind(self.view(), needle); } }
    findLast   &self needle:str -> Option<long> { unsafe { return strFindLast(self.view(), needle); } }
    slice      &self from:long n:long -> str { unsafe { return strSlice(self.view(), from, n); } }
}

// `==` compares CONTENTS, against either right-hand type: `Eq<str>` covers every literal
// (`s == "while"`), `Eq<String>` two built values. Two distinct implementations of one trait,
// and the operand picks. `Ord` and `Hash` agree with it, so a String is a map key and sorts.
methods String for Eq<str> {
    eq &self other:str -> bool { unsafe { return strEq(self.view(), other); } }
}
methods String for Eq<String> {
    eq &self other:String -> bool { unsafe { return strEq(self.view(), other.view()); } }
}
methods String for Ord {
    cmp &self other:String -> int { unsafe { return strCmp(self.view(), other.view()); } }
}
methods String for Hash {
    hash &self -> u64 { unsafe { return strHash(self.view()) as u64; } }
}

// A String owning a copy of `s`, so it outlives whatever `s` was borrowed from.
pub stringOf s:str -> String {
    out: String;
    out.pushStr(s);
    return out;
}

// ─── `+` ────────────────────────────────────────────────────────────────────
// `a + b` APPENDS. The left operand is taken by value, so this is the same buffer coming back
// out, grown — not a new one — and `a + b + c` costs one allocation's worth of growth rather than
// two whole strings. `a` is moved by the call, so using it afterwards is a compile error, which is
// exactly the property that makes reusing its buffer safe.
//
// There is deliberately no `Add` for `str`: two views have nowhere to put the result, so
// `"a" + "b"` stays an error rather than quietly allocating.
methods String for Add<str> {
    add self other:str -> String { self.pushStr(other); return self; }
}
methods String for Add<String> {
    add self other:String -> String { self.pushString(other); return self; }
}

// ─── format ─────────────────────────────────────────────────────────────────
// `format` is `println` that answers with a String instead of writing to stdout: same
// placeholders, same arguments, same `Display` impls. One allocation's worth of growth, not one
// per piece — the String IS the sink, so the formatter appends straight into it.
pub format fmt:str rest:...any -> String {
    s: String;
    // `writeArgs`, not `writeTo`: `rest` is already a collected `[any]`, and handing that to a
    // variadic would pass it as a single argument the formatter would refuse to print.
    writeArgs(s, fmt, rest);
    return s;
}
