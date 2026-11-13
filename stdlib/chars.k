// Reading a byte out of a `str`, and asking what kind of character it is.
//
// A `str` is a {ptr, len} pair with no indexing of its own — `s as [u8]` gives you a bounds-
// checked slice, but a scanner wants "the byte at i, or nothing" rather than a trap at the end,
// because running off the end is the normal way a scan finishes. `charAt` answers -1 there,
// which is why it returns a `long` and why every predicate here takes one.
//
//     i: long = 0;
//     while (isSpace(charAt(s, i))) { i = i + 1; }     // stops at the end without a length test
//
// Its own module, like `path`, because it needs nothing: no allocator, no `String`, no `Vec`, so
// the lexer-shaped code that wants it does not compile the containers to get it.
//
// All ASCII. A byte above 127 is part of a UTF-8 sequence, and none of these claim to know what
// that sequence means — they answer false, which is right for every one of them.

// The byte at `i`, or -1 past either end. Bounds-checked, which is what makes it safe: running
// off the end answers -1 rather than reading whatever follows the buffer.
pub charAt s:str i:long -> long {
    if (i < 0 || i >= s.len) { return -1; }
    unsafe { p: *u8 = s.ptr as *u8; return p[i]; }
}

pub isDigit c:long -> bool { return c >= '0' && c <= '9'; }
pub isAlpha c:long -> bool { return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'); }
pub isAlnum c:long -> bool { return isAlpha(c) || isDigit(c); }
pub isUpper c:long -> bool { return c >= 'A' && c <= 'Z'; }
pub isLower c:long -> bool { return c >= 'a' && c <= 'z'; }
pub isHexDigit c:long -> bool { return hexVal(c) >= 0; }
pub isOctDigit c:long -> bool { return c >= '0' && c <= '7'; }
// Printable ASCII, space included; and the printable characters that are neither a letter, a
// digit nor a space.
pub isPrint c:long -> bool { return c >= ' ' && c <= '~'; }
pub isPunct c:long -> bool { return isPrint(c) && c != ' ' && !isAlnum(c); }

// Space, tab, newline, carriage return, vertical tab and form feed — C's `isspace` set.
pub isSpace c:long -> bool {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\v' || c == '\f';
}

// What may start an identifier, and what may continue one. The rule every language in this
// family shares, so it is here rather than in whichever lexer needed it first.
pub isIdentStart c:long -> bool { return isAlpha(c) || c == '_'; }
pub isIdentPart  c:long -> bool { return isAlnum(c) || c == '_'; }

// Value of a hex digit, or -1 if it is not one.
pub hexVal c:long -> long {
    if (c >= '0' && c <= '9') { return c - '0'; }
    if (c >= 'a' && c <= 'f') { return c - 'a' + 10; }
    if (c >= 'A' && c <= 'F') { return c - 'A' + 10; }
    return -1;
}

// The byte a backslash escape stands for: `escapeByte('n')` is 10. The C family's set, which
// this language shares -- \n \t \r \0 \v \f, and a quote or backslash that stands for itself.
// An UNRECOGNIZED escape is the character itself, which is what makes that last case need no
// entry: `\\` and `\"` fall out of the default.
pub escapeByte e:long -> long {
    if (e == 'n') { return '\n'; }
    if (e == 't') { return '\t'; }
    if (e == 'r') { return '\r'; }
    if (e == '0') { return '\0'; }
    if (e == 'v') { return '\v'; }
    if (e == 'f') { return '\f'; }
    return e;
}

// Value of a digit in any base up to 36 (`0-9`, then `a-z` or `A-Z`), or -1 if `c` is not a
// digit of that base.
pub digitVal c:long base:long -> long {
    v: long = -1;
    if (isDigit(c)) { v = c - '0'; }
    else if (isLower(c)) { v = c - 'a' + 10; }
    else if (isUpper(c)) { v = c - 'A' + 10; }
    if (v >= base) { return -1; }
    return v;
}

// Case conversion, ASCII only: a byte outside A-Z / a-z is its own answer.
pub toUpper c:long -> long { if (isLower(c)) { return c - 'a' + 'A'; } return c; }
pub toLower c:long -> long { if (isUpper(c)) { return c - 'A' + 'a'; } return c; }

// `n` bytes from `from`, as a view INTO `s`. Out of range is clamped rather than trapped: a
// substring past the end is empty, not a bug.
pub strSlice s:str from:long n:long -> str {
    start: long = from;
    if (start < 0)      { start = 0; }
    if (start > s.len)  { start = s.len; }
    count: long = n;
    if (count < 0)                { count = 0; }
    if (start + count > s.len)    { count = s.len - start; }
    unsafe {
        p: *u8 = (s.ptr + start) as *u8;
        return p[..count] as str;
    }
}
