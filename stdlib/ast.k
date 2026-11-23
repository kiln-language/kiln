// The syntax tree as a value.
//
// This is what a macro receives and returns: a program, or a piece of one, that can be held,
// walked with `match`, taken apart and put back together like any other data. `quote { … }`
// builds one from written syntax; splicing (`@x` inside a quote, or returning one from a
// macro) turns it back into code the compiler then checks and compiles exactly as if a person
// had written it.
//
// It is a copy of the tree, not a handle into the compiler's own arena, so a macro cannot change
// the program it was called from. It can only produce a new piece, which the compiler splices in
// itself. That keeps hygiene enforceable, at the cost of one copy per macro use.
//
// Every variant mirrors one shape the compiler's parser produces (see `4-parse/ast.k` in the
// compiler); nothing here is a second design of the language's syntax. The compiler builds and
// reads these by name (the variants, `newBox`, `nodeList`/`nameList` and their `with`/`done`),
// so renaming any of them is a change to the compiler too.
#include <{core, vec, heap, panic, string, chars}>

// What an operator between two operands is.
pub enum BinOp: int {
    Add, Sub, Mul, Div, Mod,
    Lt, Gt, Le, Ge, Eq, Ne,
    BitAnd, BitOr, BitXor, Shl, Shr,
    And, Or,
    Assign
}

// What a prefix operator is.
pub enum UnOp: int { Neg, Not, BitNot, Deref, AddrOf }

// One node of the tree. A leaf holds its value; a branch holds its children by value, so a
// `Node` owns its whole subtree and dropping it releases all of it.
pub enum Node {
    // ─── leaves ───────────────────────────────────────────────────────────────
    Int(long),                       // an integer literal, at whatever width the source gave it
    Str(str),                        // a string literal, the text between the quotes
    Name(str),                       // a variable, as written
    Sizeof(str),                     // sizeof(T), naming the type
    Nameof(str, Box<Node>),          // nameof(E, v)

    // ─── expressions ──────────────────────────────────────────────────────────
    Binary(BinOp, Box<Node>, Box<Node>),
    Unary(UnOp, Box<Node>),
    Cast(Box<Node>, str),            // `e as T`, naming the type
    Call(str, Vec<Node>),            // `f(a, b)`
    Method(Box<Node>, str, Vec<Node>),
    Field(Box<Node>, str),           // `e.f`
    Index(Box<Node>, Box<Node>),     // `e[i]`
    StructLit(str, Vec<str>, Vec<Node>),   // `T { f: v, … }`: the names, and the values in the same order
    TupleLit(Vec<Node>),

    // ─── statements ───────────────────────────────────────────────────────────
    // A quote of `{ ... }` is a Block; a macro returning one is spliced as statements.
    Nothing,                         // an absent piece: no `else`, no initializer, a bare `return`
    Block(Vec<Node>),
    ExprStmt(Box<Node>),
    Let(str, str, Box<Node>),        // `name: T = init;`: the type by its spelling, Nothing for no initializer
    If(Box<Node>, Box<Node>, Box<Node>),   // condition, then-block, and the else: a Block, an If, or Nothing
    While(Box<Node>, Box<Node>),
    Return(Box<Node>),               // the value, or Nothing
    Break,
    Continue,

    // ─── the splice ───────────────────────────────────────────────────────────
    // `@x` inside a quote is compiled to `x.clone()`, so a quoted tree never holds one of these
    // by the time it is built; the variant stays for a tree assembled by hand.
    Splice(str),

    // ─── declarations: what a derive macro returns ────────────────────────────
    // Appended after `Splice` and never reordered: the compiler names every variant by spelling,
    // and a seed compiler builds trees for its own `vec!`/`map!` against this declaration.
    // A type is spelled as the compiler mangles it: `long`, `mod::Point`, `ref_mod::Point` for
    // `&Point`, `ptr_u8` for `*u8`, `slice_u8` for `[u8]`, and `Self` / `ref_Self` for the type
    // the methods are for.
    MethodsDecl(str, str, Vec<Node>),       // `methods T for Trait { ... }`: the type and the trait by spelling ("" for no trait), and its FnDecls
    FnDecl(str, Vec<Node>, str, Box<Node>), // a method: its name, its ParamDecls (a receiver first, named `self`), the return type, the body Block
    ParamDecl(str, str, str),               // name, type, and convention: "", "inout", "sink" or "read"
    VariantLit(str, str, Vec<Node>),        // `E.V(a, b)`: the enum and the variant by spelling, and the payload values
    Float(str)                              // a float literal, as written
}

// A deep copy: every child through its Box, every list element by element. `@x` in a quote
// is this, so one Node may be spliced into several places.
methods Node for Clone {
    clone &self -> Node {
        match self {
            Int(v)     { return Node.Int(v); }
            Str(s)     { return Node.Str(s); }
            Name(s)    { return Node.Name(s); }
            Sizeof(s)  { return Node.Sizeof(s); }
            Nameof(e, v)    { return Node.Nameof(e, newBox(v.at().clone())); }
            Binary(op, l, r) { return Node.Binary(op, newBox(l.at().clone()), newBox(r.at().clone())); }
            Unary(op, e)    { return Node.Unary(op, newBox(e.at().clone())); }
            Cast(e, t)      { return Node.Cast(newBox(e.at().clone()), t); }
            Call(f, args)   { return Node.Call(f, cloneNodes(args)); }
            Method(r, m, args) { return Node.Method(newBox(r.at().clone()), m, cloneNodes(args)); }
            Field(b, f)     { return Node.Field(newBox(b.at().clone()), f); }
            Index(b, i)     { return Node.Index(newBox(b.at().clone()), newBox(i.at().clone())); }
            StructLit(t, names, vals) { return Node.StructLit(t, cloneNames(names), cloneNodes(vals)); }
            TupleLit(vals)  { return Node.TupleLit(cloneNodes(vals)); }
            Nothing         { return Node.Nothing; }
            Block(items)    { return Node.Block(cloneNodes(items)); }
            ExprStmt(e)     { return Node.ExprStmt(newBox(e.at().clone())); }
            Let(n, t, i)    { return Node.Let(n, t, newBox(i.at().clone())); }
            If(c, t, e)     { return Node.If(newBox(c.at().clone()), newBox(t.at().clone()), newBox(e.at().clone())); }
            While(c, b)     { return Node.While(newBox(c.at().clone()), newBox(b.at().clone())); }
            Return(v)       { return Node.Return(newBox(v.at().clone())); }
            Break           { return Node.Break; }
            Continue        { return Node.Continue; }
            Splice(s)       { return Node.Splice(s); }
            MethodsDecl(t, tr, fns) { return Node.MethodsDecl(t, tr, cloneNodes(fns)); }
            FnDecl(n, ps, r, b)     { return Node.FnDecl(n, cloneNodes(ps), r, newBox(b.at().clone())); }
            ParamDecl(n, t, c)      { return Node.ParamDecl(n, t, c); }
            VariantLit(e, v, args)  { return Node.VariantLit(e, v, cloneNodes(args)); }
            Float(s)                { return Node.Float(s); }
        }
    }
}
pub cloneNodes xs:&Vec<Node> -> Vec<Node> {
    out: Vec<Node>;
    out.reserve(xs.len());
    for x in xs { out.push(x.clone()); }
    return out;
}
pub cloneNames xs:&Vec<str> -> Vec<str> {
    out: Vec<str>;
    out.extend(xs);
    return out;
}

// The tree back as source text, for a message that quotes what was written: parentheses go
// around every binary operation, which is always correct and never ambiguous, and anything
// without an obvious spelling prints as `<expr>`. `sourceOf` strips the outermost pair, so
// `a == b` reads back as `a == b`, not `(a == b)`.
pub sourceOf inout n:Node -> String {
    s: String;
    unparseInto(n, &s);
    inner: String;
    unsafe {
        v: str = s.view();
        if (v.len > 2 && charAt(v, 0) == '(' && charAt(v, v.len - 1) == ')') { inner.pushStr(strSlice(v, 1, v.len - 2)); }
        else { inner.pushStr(v); }
    }
    return inner;
}
local unparseInto inout n:Node inout out:String -> void {
    match n {
        Int(v)  { out.pushLong(v); }
        Str(s)  { out.push('"'); out.pushStr(s); out.push('"'); }
        Name(s) { out.pushStr(s); }
        Binary(op, l, r) {
            out.push('('); unparseInto(l.at(), out); out.push(' '); out.pushStr(binOpText(op));
            out.push(' '); unparseInto(r.at(), out); out.push(')');
        }
        Unary(op, e) { out.pushStr(unOpText(op)); unparseInto(e.at(), out); }
        Call(f, args) { out.pushStr(f); out.push('('); unparseAll(&args, out); out.push(')'); }
        Method(r, m, args) { unparseInto(r.at(), out); out.push('.'); out.pushStr(m); out.push('('); unparseAll(&args, out); out.push(')'); }
        Field(b, f) { unparseInto(b.at(), out); out.push('.'); out.pushStr(f); }
        Index(b, i) { unparseInto(b.at(), out); out.push('['); unparseInto(i.at(), out); out.push(']'); }
        Cast(e, t)  { out.push('('); unparseInto(e.at(), out); out.pushStr(" as "); out.pushStr(t); out.push(')'); }
        Sizeof(t)   { out.pushStr("sizeof("); out.pushStr(t); out.push(')'); }
        _ { out.pushStr("<expr>"); }
    }
}
local unparseAll inout args:Vec<Node> inout out:String -> void {
    for i in 0..args.len() { if (i > 0) { out.pushStr(", "); } unparseInto(args.at(i), out); }
}
// The operators as written, in the order of their enums: data, computed when this file is
// compiled (and read by macros that call `sourceOf` while they run).
local gBinOpText: Vec<str> = vec!["+", "-", "*", "/", "%", "<", ">", "<=", ">=", "==", "!=", "&", "|", "^", "<<", ">>", "&&", "||", "="];
local gUnOpText: Vec<str> = vec!["-", "!", "~", "*", "&"];
local binOpText op:BinOp -> str { return gBinOpText.get(op as long); }
local unOpText op:UnOp -> str { return gUnOpText.get(op as long); }

// The compiler's own parser, for a macro handed raw text (`name![ ... ]`): the piece read as
// one expression, its names resolved where the macro was called. A builtin: the compiler answers
// it while a macro runs, and it has no runtime.
pub builtin parseExpr src:str -> Node;

// ─── reading raw text: what a `name![ ... ]` macro does with what it is handed ──────────────

// The pieces between top-level commas (outside every bracket and literal), trimmed. A gap
// between two commas is refused, naming the macro; a trailing comma is allowed, and nothing at
// all is no pieces.
pub splitTopLevel text:str who:str -> Vec<str> {
    out: Vec<str>;
    start: long = 0;
    depth: long = 0;
    i: long = 0;
    while (i <= text.len) {
        c: long = -1;
        if (i < text.len) { c = charAt(text, i); }
        if (c == '"' || c == '\'') { i = literalEnd(text, i); continue; }
        if (c == '(' || c == '[' || c == '{') { depth = depth + 1; }
        if (c == ')' || c == ']' || c == '}') { depth = depth - 1; }
        if ((c == ',' && depth == 0) || c == -1) {
            piece: str = strTrim(strSlice(text, start, i - start));
            if (piece.len == 0) {
                if (c == ',') {
                    msg: String = stringOf(who) + ": empty element between commas";
                    unsafe { panic(msg.view()); }
                }
            } else { out.push(piece); }
            start = i + 1;
        }
        i += 1;
    }
    return out;
}

// Each piece read as code, cast to `tname` when one was named.
pub parseEach pieces:Vec<str> tname:str -> Vec<Node> {
    out: Vec<Node>;
    for piece in pieces {
        e: Node = parseExpr(piece);
        if (tname.len > 0) { e = Node.Cast(newBox(e), tname); }
        out.push(e);
    }
    return out;
}

// The `T:` at the front (`K, V:` for `count` 2) taken off: the names, trimmed, and the rest.
// No prefix: no names, and the whole text.
pub struct RawText { names: Vec<str>, rest: str }
pub takePrefix text:str count:long -> RawText {
    names: Vec<str>;
    p: long = typePrefixEnd(text, count);
    if (p < 0) { return RawText { names: names, rest: text }; }
    parts: Vec<str> = strSplit(strSlice(text, 0, p), ',');
    for x in parts { names.push(strTrim(x)); }
    return RawText { names: names, rest: strSlice(text, p + 1, text.len - p - 1) };
}
// The colon's position when the text starts with identifiers and one colon (`T:`, or `K, V:`
// for `count` 2), or -1. A `::` is a qualified name, not a prefix.
pub typePrefixEnd s:str count:long -> long {
    i: long = 0;
    n: long = 0;
    while (n < count) {
        while (i < s.len && isSpace(charAt(s, i))) { i = i + 1; }
        if (i >= s.len || !isIdentStart(charAt(s, i))) { return -1; }
        while (i < s.len && isIdentPart(charAt(s, i))) { i = i + 1; }
        while (i < s.len && isSpace(charAt(s, i))) { i = i + 1; }
        n += 1;
        if (n < count) {
            if (i >= s.len || charAt(s, i) != ',') { return -1; }
            i += 1;
        }
    }
    if (i >= s.len || charAt(s, i) != ':') { return -1; }
    if (i + 1 < s.len && charAt(s, i + 1) == ':') { return -1; }
    return i;
}

// Past the string or character literal opening at `i`, minding its escapes.
pub literalEnd s:str i:long -> long {
    q: long = charAt(s, i);
    j: long = i + 1;
    while (j < s.len) {
        c: long = charAt(s, j);
        if (c == '\\') { j = j + 2; continue; }
        if (c == q) { return j + 1; }
        j += 1;
    }
    return s.len;
}

// The list builder a `quote` compiles to. A quote is an expression, and `{ v: Vec<Node>;
// v.push(a); … v }` has no expression form; nor can a variadic carry an owning value out of its
// slice. So a child list is a chain: `nodeList().with(a).with(b).done()`, each `with` consuming
// the builder and handing it back, which is expressible anywhere a value is.
pub struct NodeList { items: Vec<Node> }
pub nodeList -> NodeList { v: Vec<Node>; return NodeList { items: v }; }
methods NodeList {
    with self n:Node -> NodeList { self.items.push(n); return self; }
    done self -> Vec<Node> { return self.items; }
}
pub struct NameList { items: Vec<str> }
pub nameList -> NameList { v: Vec<str>; return NameList { items: v }; }
methods NameList {
    with self n:str -> NameList { self.items.push(n); return self; }
    done self -> Vec<str> { return self.items; }
}

// A splice standing as a statement of a quoted block, `{ @x }`, adds to the list being built
// whatever `x` holds: one Node, or every Node of a `Vec<Node>` in order. That is how a macro
// splices a run of statements it built in a loop. The parser cannot know which `x` is, so the
// quote calls `add` and the argument's type picks the implementation.
pub trait QuoteAdd<T> { add self x:&T -> NodeList; }
methods NodeList for QuoteAdd<Node> {
    add self x:&Node -> NodeList { self.items.push(x.clone()); return self; }
}
methods NodeList for QuoteAdd<Vec<Node>> {
    add self xs:&Vec<Node> -> NodeList {
        self.items.reserve(xs.len());
        for x in xs { self.items.push(x.clone()); }
        return self;
    }
}
