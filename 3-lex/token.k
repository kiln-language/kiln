// What the lexer produces.
//
// A token is a kind and, for the four kinds that carry one, a value. Identifiers and string
// literals carry an interned `Sym`; integer and char literals carry the number itself. Both
// fields are plain integers, so a `Token` is Copy and a `Vec<Token>` reads back with `get`.
#include <support::compiler>
#include <stdlib::{chars, fmt, string, vec}>

pub enum Tok: int {
    Id,
    AtSign, Colon, Semicolon, Comma, Dot,
    LeftParen, RightParen, LeftCurly, RightCurly, LeftSquare, RightSquare,
    LessThan, GreaterThan,
    Plus, Dash, Star, Slash, Percent,
    Arrow, Ellipsis, DotDot,
    Equals, Exclamation, Ampersand, Pipe, QuotationMark, Apostrophe, Hash,
    IsEqual, IsNotEqual, IsLessOrEqual, IsGreaterOrEqual,
    FileEnd,
    Literal, IntLiteral, LongLiteral, CharLiteral, StringLiteral, BooleanLiteral,
    Caret, Tilde, ShiftLeft, ShiftRight, LogicalAnd, LogicalOr,
    ColonColon,
    FloatLiteral,       // `1.5`, `2e10`: the spelling, converted where its type is known
    U64Literal,         // past `long`'s maximum (to 2^64 - 1): the bits, which only a u64 takes
    Question,           // `f()?`: hand a failure back to the caller
    // Compound assignment, `x += y`: one each, so a statement says what it is in its first token
    // after the place.
    PlusEq, MinusEq, StarEq, SlashEq, PercentEq, AmpEq, PipeEq, CaretEq, ShlEq, ShrEq
}

pub struct Token {
    kind: Tok,
    text: Sym,     // Id, Literal, StringLiteral, FloatLiteral: the spelling. NO_SYM otherwise.
    num:  long     // IntLiteral, LongLiteral, CharLiteral: the value; U64Literal: its bits.
}

pub tokenOf k:Tok -> Token       { return Token { kind: k, text: NO_SYM, num: 0 }; }
pub tokenText k:Tok s:Sym -> Token { return Token { kind: k, text: s, num: 0 }; }
pub tokenNum k:Tok n:long -> Token { return Token { kind: k, text: NO_SYM, num: n }; }

// ─── lookup tables ───────────────────────────────────────────────────────────
//
// Every key here is a dense small integer (a `Tok`, an ASCII byte) so the index is the lookup,
// and no answer is a chain of comparisons paying one test for every entry ahead of the one it
// wants. Three of the four are on the lexer's hot path and run once per character or per token:
// `charClass` decides what `next` does with a character, `twoCharOf` whether it starts a
// two-character operator, and `punctOf` which single-character kind it is.
//
// Built by `Default`, so the tables exist before `main`'s first statement and no accessor has to
// test whether they do. The arrays are inline, so this is `.bss` and a fill. Nothing allocates.

local ASCII: long = 128;   // the length of every byte-keyed table below
// How many `Tok` there are, counted from the enum rather than written out beside it: `nameof`
// answers `?` past the last variant, and this runs when the compiler is compiled, so the count is
// a constant by the time anything reads it.
//
// `TokTables.spell` is sized by `SPELL_SLOTS`, not by that count: an array's length is folded
// when the struct is parsed, and the count is only known once the evaluator has run. `countToks`
// is what keeps the two honest: a `Tok` added without raising `SPELL_SLOTS` stops the fold with a
// message rather than reading past the end of the table.
local SPELL_SLOTS: long = 64;      // the length of `TokTables.spell`: at least the number of `Tok`
local TOK_COUNT: long = countToks();

local countToks -> long {
    n: long = 0;
    while (!strEq(nameof(Tok, n as Tok), "?")) { n = n + 1; }
    if (n > SPELL_SLOTS) {
        panic("Tok has outgrown TokTables.spell: raise SPELL_SLOTS");
    }
    return n;
}

// What `next` does with a character. The C++ lexer asked this as a run of predicate calls in a
// fixed order: `isspace`, then `/`, then `#`, then `isalpha||_`, then `isdigit`, then the quotes,
// then `.`, so a semicolon paid every one of them before reaching the punctuation map. The
// classes are disjoint, which is what lets one table read replace the whole run and still answer
// exactly what the run answered.
pub enum CharClass: int {
    Punct,     // anything else: a two-character operator, or the single-character table
    Space,
    Slash,     // `//`, `/* */`, or division
    Hash,      // a preprocessor marker
    Ident,
    Digit,
    DQuote,
    SQuote,
    Dot        // `.`, `..` or `...`
}

// A two-character operator, keyed by its first character. Two slots is enough: `<` starts `<<`
// and `<=`, `>` starts `>>` and `>=`, and every other lead starts exactly one.
//
// An empty slot is `NO_PARTNER`, which is -2 rather than 0 or -1 because both of those are
// characters the lexer can really be holding (a NUL byte in the source, and the -1 `peek`
// answers at end of input) and neither may be allowed to match an entry that is not there.
local NO_PARTNER: long = -2;

local struct TwoCharOp { p1: long, t1: Tok, p2: long, t2: Tok }

local struct TokTables {
    // The text the C++ lexer stored as a token's `value`, indexed by the kind, and empty (which
    // the zero fill a partial literal does already makes it) for the kinds that carry a value of
    // their own. Real data: nothing about `+` says its spelling is "+". The kind's printed name is
    // not here; the declaration above already says it, and `tokName` reads it from there.
    spell: [str; SPELL_SLOTS],    // checked against Tok by countToks
    punct: [Tok; ASCII],          // the single-character kind, or Tok.FileEnd for "not one"
    cls:   [CharClass; ASCII],    // what `next` does with it
    two:   [TwoCharOp; ASCII]     // the two-character operators it can start
}

methods TokTables for Default {
    new -> TokTables {
        t: TokTables = TokTables { };   // array fields zero-filled; naming the type skips Default

        // One pass over the byte-keyed tables. The character classes come from the same
        // `stdlib::chars` predicates the lexer would otherwise call per character, so the table
        // is derived from them rather than a second copy of the rule that could drift.
        for i in 0..ASCII {
            t.punct[i] = Tok.FileEnd;
            t.two[i]   = TwoCharOp { p1: NO_PARTNER, t1: Tok.FileEnd, p2: NO_PARTNER, t2: Tok.FileEnd };
            k: CharClass = CharClass.Punct;
            if      (isSpace(i))      { k = CharClass.Space; }
            else if (isIdentStart(i)) { k = CharClass.Ident; }
            else if (isDigit(i))      { k = CharClass.Digit; }
            t.cls[i] = k;
        }
        t.cls['/']  = CharClass.Slash;   t.cls['#']  = CharClass.Hash;
        t.cls['"']  = CharClass.DQuote;  t.cls['\''] = CharClass.SQuote;
        t.cls['.']  = CharClass.Dot;

        t.two['-'] = TwoCharOp { p1: '>', t1: Tok.Arrow,      p2: '=', t2: Tok.MinusEq };
        t.two['&'] = TwoCharOp { p1: '&', t1: Tok.LogicalAnd, p2: '=', t2: Tok.AmpEq };
        t.two['|'] = TwoCharOp { p1: '|', t1: Tok.LogicalOr,  p2: '=', t2: Tok.PipeEq };
        t.two['+'] = TwoCharOp { p1: '=', t1: Tok.PlusEq,     p2: NO_PARTNER, t2: Tok.FileEnd };
        t.two['*'] = TwoCharOp { p1: '=', t1: Tok.StarEq,     p2: NO_PARTNER, t2: Tok.FileEnd };
        t.two['/'] = TwoCharOp { p1: '=', t1: Tok.SlashEq,    p2: NO_PARTNER, t2: Tok.FileEnd };
        t.two['%'] = TwoCharOp { p1: '=', t1: Tok.PercentEq,  p2: NO_PARTNER, t2: Tok.FileEnd };
        t.two['^'] = TwoCharOp { p1: '=', t1: Tok.CaretEq,    p2: NO_PARTNER, t2: Tok.FileEnd };
        t.two[':'] = TwoCharOp { p1: ':', t1: Tok.ColonColon, p2: NO_PARTNER, t2: Tok.FileEnd };
        t.two['='] = TwoCharOp { p1: '=', t1: Tok.IsEqual,    p2: NO_PARTNER, t2: Tok.FileEnd };
        t.two['!'] = TwoCharOp { p1: '=', t1: Tok.IsNotEqual, p2: NO_PARTNER, t2: Tok.FileEnd };
        t.two['<'] = TwoCharOp { p1: '<', t1: Tok.ShiftLeft,  p2: '=', t2: Tok.IsLessOrEqual    };
        t.two['>'] = TwoCharOp { p1: '>', t1: Tok.ShiftRight, p2: '=', t2: Tok.IsGreaterOrEqual };

        // The kinds that are pure punctuation. The eight that carry a value of their own are not
        // written: `TokTables { }` names fewer fields than the struct has, so the whole slot is
        // zeroed before anything is stored into it, and a zeroed `str` is "". Two to a line, as
        // the byte-keyed tables below are; with the name gone these are one short assignment each.
        t.spell[Tok.AtSign as long]        = "@";    t.spell[Tok.Colon as long]        = ":";
        t.spell[Tok.Semicolon as long]     = ";";    t.spell[Tok.Comma as long]        = ",";
        t.spell[Tok.Dot as long]           = ".";    t.spell[Tok.LeftParen as long]    = "(";
        t.spell[Tok.RightParen as long]    = ")";    t.spell[Tok.LeftCurly as long]    = "{";
        t.spell[Tok.RightCurly as long]    = "}";    t.spell[Tok.LeftSquare as long]   = "[";
        t.spell[Tok.RightSquare as long]   = "]";    t.spell[Tok.LessThan as long]     = "<";
        t.spell[Tok.GreaterThan as long]   = ">";    t.spell[Tok.Plus as long]         = "+";
        t.spell[Tok.Dash as long]          = "-";    t.spell[Tok.Star as long]         = "*";
        t.spell[Tok.Slash as long]         = "/";    t.spell[Tok.Percent as long]      = "%";
        t.spell[Tok.Arrow as long]         = "->";   t.spell[Tok.Ellipsis as long]     = "...";
        t.spell[Tok.DotDot as long]        = "..";   t.spell[Tok.Equals as long]       = "=";
        t.spell[Tok.Exclamation as long]   = "!";    t.spell[Tok.Ampersand as long]    = "&";
        t.spell[Tok.Pipe as long]          = "|";    t.spell[Tok.QuotationMark as long] = "\"";
        t.spell[Tok.Apostrophe as long]    = "'";    t.spell[Tok.Hash as long]         = "#";
        t.spell[Tok.IsEqual as long]       = "==";   t.spell[Tok.IsNotEqual as long]   = "!=";
        t.spell[Tok.IsLessOrEqual as long] = "<=";   t.spell[Tok.IsGreaterOrEqual as long] = ">=";
        t.spell[Tok.Caret as long]         = "^";    t.spell[Tok.Tilde as long]        = "~";
        t.spell[Tok.ShiftLeft as long]     = "<<";   t.spell[Tok.ShiftRight as long]   = ">>";
        t.spell[Tok.LogicalAnd as long]    = "&&";   t.spell[Tok.LogicalOr as long]    = "||";
        t.spell[Tok.ColonColon as long]    = "::";   t.spell[Tok.Question as long]     = "?";
        t.spell[Tok.PlusEq as long]        = "+=";   t.spell[Tok.MinusEq as long]      = "-=";
        t.spell[Tok.StarEq as long]        = "*=";   t.spell[Tok.SlashEq as long]      = "/=";
        t.spell[Tok.PercentEq as long]     = "%=";   t.spell[Tok.AmpEq as long]        = "&=";
        t.spell[Tok.PipeEq as long]        = "|=";   t.spell[Tok.CaretEq as long]      = "^=";
        t.spell[Tok.ShlEq as long]         = "<<=";  t.spell[Tok.ShrEq as long]        = ">>=";

        t.punct['@']  = Tok.AtSign;      t.punct[':']  = Tok.Colon;
        t.punct[';']  = Tok.Semicolon;   t.punct[',']  = Tok.Comma;
        t.punct['.']  = Tok.Dot;         t.punct['(']  = Tok.LeftParen;
        t.punct[')']  = Tok.RightParen;  t.punct['{']  = Tok.LeftCurly;
        t.punct['}']  = Tok.RightCurly;  t.punct['[']  = Tok.LeftSquare;
        t.punct[']']  = Tok.RightSquare; t.punct['<']  = Tok.LessThan;
        t.punct['>']  = Tok.GreaterThan; t.punct['+']  = Tok.Plus;
        t.punct['-']  = Tok.Dash;        t.punct['*']  = Tok.Star;
        t.punct['/']  = Tok.Slash;       t.punct['%']  = Tok.Percent;
        t.punct['=']  = Tok.Equals;      t.punct['!']  = Tok.Exclamation;
        t.punct['&']  = Tok.Ampersand;   t.punct['|']  = Tok.Pipe;
        t.punct['^']  = Tok.Caret;       t.punct['~']  = Tok.Tilde;
        t.punct['#']  = Tok.Hash;        t.punct['"']  = Tok.QuotationMark;
        t.punct['\''] = Tok.Apostrophe; t.punct['?']  = Tok.Question;
        return t;
    }
}

local gTok: TokTables;

// `LeftParen` -> `LEFT_PAREN`: an upper-case letter that is not the first opens a new word, and
// everything else is upper-cased where it stands. Local to this file: re-casing an identifier is
// what a compiler does to a token name, not something the rest of the language has asked for.
local screamingSnake s:str -> String {
    out: String;
    for i in 0..s.len {
        c: long = charAt(s, i);
        if (i > 0 && isUpper(c)) { out.push('_'); }
        out.push(toUpper(c) as char);
    }
    return out;
}

// One name per kind, computed when this compiler is compiled and held as data. Strings rather
// than views kept in the interner: the initializer runs at build time, where writing the
// interner (a `var`) is not a thing it may do.
local gTokNames: Vec<String> = tokNames();

local tokNames -> Vec<String> {
    t: Vec<String>;
    for i in 0..TOK_COUNT { t.push(screamingSnake(nameof(Tok, i as Tok))); }
    // The four the C++ lexer spells its own way; no re-casing of the variant produces them, so
    // they are data. The other 43 were the declaration above, written out a second time.
    t.set(Tok.DotDot as long,           stringOf("DOTDOT"));
    t.set(Tok.ColonColon as long,       stringOf("COLONCOLON"));
    t.set(Tok.IsLessOrEqual as long,    stringOf("IS_LESS_THAN_OR_EQUAL"));
    t.set(Tok.IsGreaterOrEqual as long, stringOf("IS_GREATER_THAN_OR_EQUAL"));
    return t;
}

// The name the C++ lexer printed for a kind, so a token dump from either compiler reads the same.
// Derived from the enum's own declaration rather than kept as a second copy of it, indices and all.
pub tokName k:Tok -> str {
    unsafe { return gTokNames.at(k as long).view(); }
}

// The text the C++ lexer stored as a token's `value` for the kinds that are pure punctuation.
// Empty for the kinds that carry a value of their own.
pub spellOf k:Tok -> str { return gTok.spell[k as long]; }

// The single-character kinds. `Tok.FileEnd` means "not one of these", which is also the answer
// for a byte outside ASCII: the C++ map had no entry for one either, and the lexer rejects both
// the same way. Takes the `long` the scanner already holds rather than a `char`, so a high byte
// cannot arrive here as a negative index.
pub punctOf c:long -> Tok {
    if (c < 0 || c >= ASCII) { return Tok.FileEnd; }
    return gTok.punct[c];
}

// What `next` should do with `c`. A byte outside ASCII is `Punct`, which sends it down the same
// path a `$` takes: no two-character operator and no entry in the punctuation table, so it is
// rejected, which is what the C++ lexer did with one too, having no map entry for it either.
pub charClass c:long -> CharClass {
    if (c < 0 || c >= ASCII) { return CharClass.Punct; }
    return gTok.cls[c];
}

// The two-character operator `first` and `next` spell, or `Tok.FileEnd` for "they spell none".
// Checked before the single-character table so `==` never lexes as two `=`.
pub twoCharOf first:long next:long -> Tok {
    if (first < 0 || first >= ASCII) { return Tok.FileEnd; }
    e: TwoCharOp = gTok.two[first];
    if (next == e.p1) { return e.t1; }
    if (next == e.p2) { return e.t2; }
    return Tok.FileEnd;
}

// One token as the dump prints it: the kind, then the value when there is one. Matches the C++
// `--emit=tokens` output line for line, which is the whole point of it.
//
// Appends rather than returning a String so the caller can reuse one buffer for the whole dump:
// a token stream is millions of lines on a real build.
pub pushTokenLine inout s:String t:Token -> void {
    s.pushStr(tokName(t.kind));
    if (t.kind == Tok.FileEnd) { return; }
    if (t.kind == Tok.Id || t.kind == Tok.Literal || t.kind == Tok.StringLiteral || t.kind == Tok.FloatLiteral) {
        s.push(' ');
        s.pushStr(nameOf(t.text));
    } else if (t.kind == Tok.IntLiteral || t.kind == Tok.LongLiteral) {
        s.push(' ');
        s.pushLong(t.num);          // already a lend; `&` is for the owner's call site
    } else if (t.kind == Tok.U64Literal) {
        s.push(' ');
        s.pushString(format("{}", t.num as u64));
    } else if (t.kind == Tok.CharLiteral) {
        s.push(' ');
        s.push(t.num as char);
    } else {
        spelling: str = spellOf(t.kind);
        if (spelling.len > 0) { s.push(' '); s.pushStr(spelling); }
    }
}
