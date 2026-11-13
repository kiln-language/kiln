// Text to tokens.
//
// The input is one already-preprocessed file: markers, then the source. The lexer holds a cursor
// over that text rather than a stream, so `peek` is an index and there is nothing to unget. The
// `#file` markers set the file and package a declaration belongs to, which the parser reads back.
#include <support::compiler>
#include <token>
#include <stdlib::{chars, io, string, sys, vec}>

pub EOF_CHAR: long = -1;


// The range an integer literal must fit to stay an `int` rather than becoming a `long`, and the
// largest literal there is.
local INT_MAX: long = 2147483647;
local LONG_MAX: long = 9223372036854775807;
local U64_MAX: u64 = ~(0 as u64);
local U64_TENTH: u64 = 1844674407370955161 as u64;     // U64_MAX / 10: below it, `* 10 + d` fits

pub struct Lexer {
    src:  str,
    pos:  long,
    fileLine:       long,
    charNumber:     long,
    currentFile:    Sym,
    currentPackage: Sym,
    tokLine: long,             // where the token last returned began
    tokCol:  long,
    // The last token returned was a `.`: `t.0.1` is two tuple fields, not `t.` and `0.1`.
    afterDot: bool
}

pub lexerOf source:str -> Lexer {
    return Lexer { src: source, pos: 0, fileLine: 1, charNumber: 0,
                   currentFile: NO_SYM, currentPackage: NO_SYM, tokLine: 1, tokCol: 0, afterDot: false };
}

methods Lexer {
    // `charAt` answers -1 past the end, which is what EOF_CHAR is.
    peek &self -> long { return charAt(self.src, self.pos); }

    // Consume one character, tracking the position errors are reported at. Reading past the end
    // still counts a column, because that is where the unterminated-literal errors point.
    advance &self -> long {
        c: long = self.peek();
        if (c == EOF_CHAR) { self.charNumber = self.charNumber + 1; return EOF_CHAR; }
        self.pos = self.pos + 1;
        if (c == '\n') { self.fileLine = self.fileLine + 1; self.charNumber = 0; }
        else              { self.charNumber = self.charNumber + 1; }
        return c;
    }

    // Step over a decimal digit, advancing the cursor but not the column. The C++ lexer read a
    // number's digits straight off the stream, past the counter its own `getNextChar` kept, so
    // every diagnostic after a decimal literal on the same line is reported that many columns to
    // the left. The count is part of the locations this port has to reproduce.
    takeDigit &self -> long {
        d: long = self.peek() - '0';
        self.pos = self.pos + 1;
        return d;
    }

    // Errors point at the real source: the file named by the last `#file` marker, and the line and
    // column within it. Before the first marker there is no file to name, which happens only when
    // the lexer is run on raw source rather than through the preprocessor.
    //
    // Written straight to stderr rather than through `failAt`, which puts `Error: ` in front of
    // the location. The reference builds this diagnostic as `<file>:<line>:<col>: ` followed by a
    // message its own callers wrote with the banner already inside it, so the banner lands after
    // the location, `e1.k:5:1: Error: Unclosed string literal`, verified against the reference
    // binary for all eight of this lexer's error paths. `Preprocessor.failFrom` sits here for the
    // same reason, one line further along the same argument: the reference's text is the spec,
    // and `failAt`'s order is not it.
    err &self msg:str -> void {
        eprintln("{}:{}:{}: Error: {}", self.fileName(), self.fileLine, self.charNumber, msg);
        flushErr();
        sysExit(COMPILE_FAILED);
    }
    errStr &self msg:String -> void {
        unsafe { self.err(msg.view()); }   // the view dies with this call, which never returns
    }
    // `<input>` when no `#file` marker has been seen, which is what the reference names a lexer
    // run on raw source rather than through the preprocessor.
    fileName &self -> str {
        if (self.currentFile == NO_SYM) { return "<input>"; }
        return nameOf(self.currentFile);
    }

    // An identifier starts with a letter or an underscore and continues with either plus digits.
    // The underscore start is what lets `_` be written, which is the name `match` uses for "I am
    // not going to look at this one".
    lexIdentifier &self -> Token {
        start: long = self.pos - 1;
        while (isIdentPart(self.peek())) { self.advance(); }
        text: str = strSlice(self.src, start, self.pos - start);
        if (eqNoCase(text, "true") || eqNoCase(text, "false")) {
            return tokenText(Tok.Literal, intern(text));
        }
        return tokenText(Tok.Id, intern(text));
    }

    // Decimal, or hexadecimal after `0x`. Classified by magnitude: what fits in 32 bits is an
    // `int` literal, anything larger a `long`. Accumulated as it is scanned rather than collected
    // and converted afterwards, which is one pass instead of two.
    lexNumber &self first:long -> Token {
        digits: long = self.pos - 1;    // where the message below names the literal from
        // A float: digits, then a `.` and a digit, or an exponent. `1..5` is a range and `t.0.1`
        // two tuple fields, so the `.` needs a digit after it and nothing but a number before.
        if (first != '0' || (self.peek() != 'x' && self.peek() != 'X')) {
            if (self.floatAhead()) { return self.lexFloat(digits); }
        }
        // Up to 2^64 - 1, accumulated as a u64. What is past `long`'s maximum is a `U64Literal`
        // carrying the bits, which only a `u64` place takes (`Checker.requireAssignable`). A `_`
        // between digits separates them and is otherwise nothing: `0xFFFF_FFFF`, `1_000_000`.
        value: u64 = 0 as u64;
        if (first == '0' && (self.peek() == 'x' || self.peek() == 'X')) {
            self.advance();
            digits = self.pos;          // the C++ message names the digits, not the `0x`
            if (hexVal(self.peek()) < 0) { self.err("Expected a hexadecimal number, but found nothing after '0x'"); }
            while (hexVal(self.peek()) >= 0 || (self.peek() == '_' && hexVal(charAt(self.src, self.pos + 1)) >= 0)) {
                if (self.peek() == '_') { self.advance(); continue; }
                d: long = hexVal(self.advance());
                if ((value >> (60 as u64)) != (0 as u64)) { self.tooLarge(digits, 16); }
                value = (value << (4 as u64)) | (d as u64);
            }
        } else {
            value = (first - '0') as u64;
            while (isDigit(self.peek()) || (self.peek() == '_' && isDigit(charAt(self.src, self.pos + 1)))) {
                if (self.peek() == '_') { self.advance(); continue; }
                d: u64 = self.takeDigit() as u64;
                if (value >= U64_TENTH && value > (U64_MAX - d) / (10 as u64)) { self.tooLarge(digits, 10); }
                value = value * (10 as u64) + d;
            }
        }
        v: long = value as long;
        if (v < 0) { return tokenNum(Tok.U64Literal, v); }
        if (v <= INT_MAX) { return tokenNum(Tok.IntLiteral, v); }
        return tokenNum(Tok.LongLiteral, v);
    }

    // Whether the decimal literal whose first digit was just read goes on as a float: past its
    // digits, `.` and a digit, or `e`/`E` with an optional sign and a digit.
    floatAhead &self -> bool {
        if (self.afterDot) { return false; }
        i: long = self.pos;
        while (isDigit(charAt(self.src, i)) || charAt(self.src, i) == '_') { i = i + 1; }
        c: long = charAt(self.src, i);
        if (c == '.') { return isDigit(charAt(self.src, i + 1)); }
        if (c == 'e' || c == 'E') {
            j: long = i + 1;
            if (charAt(self.src, j) == '+' || charAt(self.src, j) == '-') { j = j + 1; }
            return isDigit(charAt(self.src, j));
        }
        return false;
    }

    // The literal's spelling, as written (less any `_`), for whoever learns its type to convert.
    lexFloat &self start:long -> Token {
        while (isDigit(self.peek()) || self.peek() == '_') { self.advance(); }
        if (self.peek() == '.' && isDigit(charAt(self.src, self.pos + 1))) {
            self.advance();
            while (isDigit(self.peek()) || self.peek() == '_') { self.advance(); }
        }
        if (self.peek() == 'e' || self.peek() == 'E') {
            self.advance();
            if (self.peek() == '+' || self.peek() == '-') { self.advance(); }
            if (!isDigit(self.peek())) { self.err("a float literal's exponent needs digits"); }
            while (isDigit(self.peek())) { self.advance(); }
        }
        if (isAlpha(self.peek()) || self.peek() == '_') { self.err("unexpected character after a float literal"); }
        s: String;
        for k in start..self.pos {
            c: long = charAt(self.src, k);
            if (c != '_') { s.push(c as char); }
        }
        return tokenText(Tok.FloatLiteral, internString(s));
    }

    // The literal does not fit a `long`. Read the rest of its digits first, so the message names
    // the whole thing rather than the prefix that happened to overflow, and so the column is the
    // one the C++ lexer would have reached, which for a decimal literal is its first digit.
    tooLarge &self digits:long base:long -> void {
        if (base == 16) { while (hexVal(self.peek()) >= 0 || self.peek() == '_') { self.advance(); } }
        else            { while (isDigit(self.peek()) || self.peek() == '_') { self.advance(); } }
        s: String;
        s.pushStr("Integer literal '");
        s.pushStr(strSlice(self.src, digits, self.pos - digits));
        s.pushStr("' is out of range");
        self.errStr(s);
    }

    // Read to the closing quote. Backslash escapes are kept verbatim (they are resolved at
    // lowering) which is also what stops an escaped quote from ending the string early. The
    // quotes stay in the token's text, as they did in the C++ lexer.
    lexStringLiteral &self -> Token {
        start: long = self.pos - 1;
        while (self.peek() != '"') {
            c: long = self.advance();
            if (c == EOF_CHAR) { self.err("Unclosed string literal"); }
            if (c == '\\' && self.advance() == EOF_CHAR) { self.err("Unclosed string literal"); }
        }
        self.advance();
        return tokenText(Tok.StringLiteral, intern(strSlice(self.src, start, self.pos - start)));
    }

    // A single character in quotes, with the usual escapes. The escape is resolved to its byte
    // here, so the token carries the one character the parser turns into a literal.
    lexCharLiteral &self -> Token {
        c: long = self.advance();
        if (c == EOF_CHAR) { self.err("Unclosed char literal"); }
        if (c == '\\') {
            e: long = self.advance();
            if (e == EOF_CHAR) { self.err("Unclosed char literal"); }
            c = escapeByte(e);
        }
        if (self.advance() != '\'') {
            self.err("a char literal must be a single character closed by '");
        }
        return tokenNum(Tok.CharLiteral, c);
    }

    // A preprocessor marker. Each consumes its whole line and emits no token:
    //   #file "path" N "pkg"   the tokens that follow belong to `path`, from its line N, in `pkg`
    //   #use  "mod"            the include graph, which the scanner already has, skipped here
    // The package rides on `#file` rather than a marker of its own so the rewritten source keeps
    // one output line per input line, which is what keeps error locations exact.
    lexDirective &self -> void {
        self.skipBlanks();
        dStart: long = self.pos;
        while (isAlpha(self.peek())) { self.advance(); }
        directive: str = strSlice(self.src, dStart, self.pos - dStart);

        arg: str = self.scanForQuoted();
        self.skipBlanks();
        line: long = 0;
        hasNum: bool = isDigit(self.peek());
        while (isDigit(self.peek())) {
            d: long = self.advance() - '0';
            if (line > (LONG_MAX - d) / 10) { self.err("line number in #file is out of range"); }
            line = line * 10 + d;
        }
        // The package argument follows the line number across blanks and nothing else: anything
        // further along is trailing text, and reading a quote out of that would put a file in the
        // wrong package.
        self.skipBlanks();
        pkgArg: str = self.quotedHere();

        while (self.peek() != '\n' && self.peek() != EOF_CHAR) { self.advance(); }
        if (self.peek() == '\n') { self.advance(); }

        if (directive == "file") {
            self.currentFile = intern(arg);
            if (hasNum) { self.fileLine = line; }
            self.currentPackage = intern(pkgArg);
        }
    }

    skipBlanks &self -> void {
        while (self.peek() == ' ' || self.peek() == '\t') { self.advance(); }
    }
    // Skip forward to the next quote on this line and read what it opens. The directive's first
    // argument, which may be separated from the name by anything.
    scanForQuoted &self -> str {
        while (self.peek() != '"' && self.peek() != '\n' && self.peek() != EOF_CHAR) {
            self.advance();
        }
        return self.quotedHere();
    }

    // Read a quoted argument only if one starts at the cursor; "" otherwise.
    quotedHere &self -> str {
        if (self.peek() != '"') { return ""; }
        self.advance();
        start: long = self.pos;
        while (self.peek() != '"' && self.peek() != EOF_CHAR) { self.advance(); }
        arg: str = strSlice(self.src, start, self.pos - start);
        if (self.peek() == '"') { self.advance(); }
        return arg;
    }

    // One token, or `Tok.FileEnd` at the end of the input.
    //
    // The first thing done with a character is one table read. The C++ lexer instead ran its
    // predicates in order: `isspace`, `/`, `#`, `isalpha||_`, `isdigit`, `"`, `'`, `.`, so a
    // semicolon reached the punctuation map having failed about forty comparisons; `charClass`
    // answers the same question with an index. The classes below are exhaustive and disjoint,
    // and the two that can decline (a `/` that opens no comment, a `.` that is not `..`) fall
    // through to the same two-character and single-character tables everything else uses, which
    // is where `Tok.Slash` and `Tok.Dot` come from.
    next &self -> Token {
        t: Token = self.nextRaw();
        self.afterDot = t.kind == Tok.Dot;
        return t;
    }

    nextRaw &self -> Token {
        while (self.peek() != EOF_CHAR) {
            c: long = self.advance();
            k: CharClass = charClass(c);
            // Where the token begins, if this character begins one: what a statement's position
            // is read from. Overwritten by every character a token does not begin at.
            self.tokLine = self.fileLine;
            self.tokCol = self.charNumber;

            if (k == CharClass.Space) { continue; }
            if (k == CharClass.Ident) { return self.lexIdentifier(); }
            if (k == CharClass.Digit) { return self.lexNumber(c); }

            if (k == CharClass.Slash) {
                // Comments. A lone slash is division.
                if (self.peek() == '/') {
                    while (self.peek() != '\n' && self.peek() != EOF_CHAR) { self.advance(); }
                    continue;
                }
                if (self.peek() == '*') {
                    self.advance();
                    loop {
                        x: long = self.advance();
                        if (x == EOF_CHAR) { self.err("unterminated block comment"); }
                        if (x == '*' && self.peek() == '/') { self.advance(); break; }
                    }
                    continue;
                }
            }
            else if (k == CharClass.Hash)   { self.lexDirective(); continue; }
            else if (k == CharClass.DQuote) { return self.lexStringLiteral(); }
            else if (k == CharClass.SQuote) { return self.lexCharLiteral(); }
            else if (k == CharClass.Dot && self.peek() == '.') {
                // `...` and `..`, which need two characters of lookahead rather than one.
                self.advance();
                if (self.peek() == '.') { self.advance(); return tokenOf(Tok.Ellipsis); }
                return tokenOf(Tok.DotDot);
            }

            two: Tok = twoCharOf(c, self.peek());
            if (two != Tok.FileEnd) {
                self.advance();
                // `<<=` and `>>=`, the two three-character operators.
                if (two == Tok.ShiftLeft && self.peek() == '=') { self.advance(); return tokenOf(Tok.ShlEq); }
                if (two == Tok.ShiftRight && self.peek() == '=') { self.advance(); return tokenOf(Tok.ShrEq); }
                return tokenOf(two);
            }

            one: Tok = punctOf(c);
            // The reference has no diagnostic here at all: its `char_to_lToken.at(character)`
            // throws `std::out_of_range`, and the driver prints that exception's own text,
            // `map::at`, with no file, line or column, and worded differently by every C++
            // standard library. That is a crash rather than a message, so this port says where
            // the character is instead of reproducing it.
            if (one == Tok.FileEnd) { self.err("unexpected character"); }
            return tokenOf(one);
        }
        return tokenOf(Tok.FileEnd);
    }

    // Every token in the input, for the `--emit=tokens` dump and for any consumer that would
    // rather have the vector than the cursor.
    all &self -> Vec<Token> {
        out: Vec<Token>;
        // A token is about eight bytes of source in this language, counting the whitespace and
        // comments between them, so the whole stream is one allocation instead of the twenty
        // doublings (each copying everything already pushed) that growing from nothing costs.
        // An estimate, not a bound: `push` still grows if the guess is low.
        out.reserve(self.src.len / 8);
        loop {
            t: Token = self.next();
            out.push(t);
            if (t.kind == Tok.FileEnd) { break; }
        }
        return out;
    }
}

// ASCII case-insensitive compare, for the `true`/`false` test the C++ lexer did with toupper.
pub eqNoCase a:str b:str -> bool {
    if (a.len != b.len) { return false; }
    for i in 0..a.len {
        if (toLower(charAt(a, i)) != toLower(charAt(b, i))) { return false; }
    }
    return true;
}
