// Turns a syntax tree into the expression that builds the equivalent `Node` value: a tree of
// constructor calls shaped like the tree itself. `quote { a + 1 }` compiles to
// `Node.Binary(BinOp.Add, newBox(Node.Name("a")), newBox(Node.Int(1)))`.
//
// The parser uses it for `quote`, and the checker uses it to hand a macro the tree of an
// argument. A tree it cannot serialize is a compile error naming what it met, never a silently
// smaller tree.
#include <{ast, registry, types}>
#include <support::compiler>
#include <stdlib::{chars, fmt, string, vec}>

// The resolved names of stdlib::ast's three types, which everything built here names.
pub struct Quoter { node: Sym, binOp: Sym, unOp: Sym }

// What `@(e)` in an expression is written as until the checker knows e's type. `$` cannot begin
// a method a person writes.
pub SPLICE_METHOD: str = "$splice";

// The `BinOp` variant each binary operator becomes, in `Op` order. The two enums are declared in
// the same order, so the operator's own index is the key.
local gBinOpNames: Vec<str> = vec![
    "Assign",
    "Add",    "Sub",    "Mul",    "Div",    "Mod",
    "Lt",     "Gt",     "Le",     "Ge",     "Eq",     "Ne",
    "BitAnd", "BitOr",  "BitXor", "Shl",    "Shr",
    "And",    "Or"
];
pub binOpName op:Op -> str {
    i: long = op as long;
    if (i < 0 || i >= gBinOpNames.len()) { return ""; }
    return gBinOpNames.get(i);
}
pub unOpName op:Op -> str {
    if (op == Op.LogicalNot) { return "Not"; }
    if (op == Op.BitwiseNot) { return "BitNot"; }
    if (op == Op.Deref)      { return "Deref"; }
    return "";
}

// A name a quote takes from the macro rather than from the text: `.@(f.name)`, `@(t.name)` where
// a type is read. The parser has only a `Sym` slot there, so it writes `$@<id>`, the id of the
// expression that computes the `str`; `$` cannot begin a name a person writes.
pub splicedName held:NodeId -> Sym { return internString(format("$@{}", held)); }
pub splicedHeld n:Sym -> NodeId {
    if (n == NO_SYM) { return NO_NODE; }
    s: str = nameOf(n);
    if (s.len < 3 || charAt(s, 0) != '$' || charAt(s, 1) != '@') { return NO_NODE; }
    v: long = 0;
    for i in 2..s.len { v = v * 10 + charAt(s, i) - '0'; }
    return v;
}
local holdsSplice s:str -> bool {
    i: long = 0;
    while (i + 1 < s.len) {
        if (charAt(s, i) == '$' && charAt(s, i + 1) == '@') { return true; }
        i = i + 1;
    }
    return false;
}

methods Quoter {
    // A block's statements. A statement that is just `@x` is really a list splice: whatever `x`
    // holds (a Node, or a `Vec<Node>`) is added in its place, through `QuoteAdd` in stdlib/ast.k,
    // whose two implementations the argument's type picks between.
    quoteStmts &self inout a:Ast ids:Vec<long> -> NodeId {
        none: Vec<NodeId>;
        b: NodeId = self.qCall(a, "nodeList", none);
        for k in 0..ids.len() {
            one: Vec<NodeId>;
            held: NodeId = self.listSplice(a, ids.get(k));
            if (held != NO_NODE) {
                one.push(held);
                b = self.qMethod(a, b, "add", one);
            } else {
                one.push(self.quoteStmt(a, ids.get(k)));
                b = self.qMethod(a, b, "with", one);
            }
        }
        list: Vec<NodeId>; list.push(self.qMethod(a, b, "done", none));
        return self.qVariant(a, "Block", list);
    }
    // The held expression of a statement that is nothing but `@x`, or NO_NODE.
    listSplice &self inout a:Ast id:long -> NodeId {
        st: Stmt = a.stmts.get(id);
        if (st.kind != StmtKind.Expr) { return NO_NODE; }
        e: Expr = a.expr(a.exprStmts.get(st.at).value);
        if (e.op != Op.Splice) { return NO_NODE; }
        match e.payload { Sub(v) { return v; } _ { } }
        return NO_NODE;
    }
    // A name as the `str` a Node holds: written out, or computed by the macro (`splicedName`).
    qText &self inout a:Ast n:Sym -> NodeId {
        held: NodeId = splicedHeld(n);
        if (held != NO_NODE) { return held; }
        return self.qStr(a, n);
    }
    // A type as the spelling a Node holds (see stdlib/ast.k): mangled, or computed by the macro.
    qType &self inout a:Ast k:Lit n:Sym -> NodeId {
        if (n != NO_SYM && k == Lit.Struct) {
            held: NodeId = splicedHeld(n);
            if (held != NO_NODE) { return held; }
        }
        spelled: str = typeMangleName(k, n);
        if (holdsSplice(spelled)) {
            failStr(stringOf("a spliced type name inside a larger type is not supported in a `quote`\nhelp: build the whole spelling (`ref_T`, `ptr_T`) in the macro and splice that"));
        }
        return self.qStr(a, intern(spelled));
    }
    quoteBlock &self inout a:Ast b:long -> NodeId {
        ids: Vec<long>;
        for k in 0..a.blockLen(b) { ids.push(a.stmtIdAt(b, k)); }
        return self.quoteStmts(a, ids);
    }
    // A statement as the Node that builds it.
    quoteStmt &self inout a:Ast id:long -> NodeId {
        st: Stmt = a.stmts.get(id);
        if (st.kind == StmtKind.Expr || st.kind == StmtKind.Call) {
            one: Vec<NodeId>; one.push(self.qBoxed(a, self.quoteTree(a, a.exprStmts.get(st.at).value)));
            return self.qVariant(a, "ExprStmt", one);
        }
        if (st.kind == StmtKind.VarDecl) {
            d: VarDeclNode = a.decls.get(st.at);
            if (d.isArray) { failStr(stringOf("an array declaration is not supported inside a `quote` yet")); }
            args: Vec<NodeId>;
            args.push(self.qStr(a, d.name));
            args.push(self.qType(a, d.kind, d.structName));
            if (d.init != NO_NODE) { args.push(self.qBoxed(a, self.quoteTree(a, d.init))); }
            else { args.push(self.qBoxed(a, self.qNothing(a))); }
            return self.qVariant(a, "Let", args);
        }
        if (st.kind == StmtKind.If) { return self.quoteIf(a, st.at); }
        if (st.kind == StmtKind.While) {
            w: WhileNode = a.whiles.get(st.at);
            if (w.step >= 0) { failStr(stringOf("a `for` loop is not supported inside a `quote` yet")); }
            args: Vec<NodeId>;
            args.push(self.qBoxed(a, self.quoteTree(a, w.cond)));
            args.push(self.qBoxed(a, self.quoteBlock(a, w.body)));
            return self.qVariant(a, "While", args);
        }
        if (st.kind == StmtKind.Return) {
            r: ReturnNode = a.returns.get(st.at);
            one: Vec<NodeId>;
            if (r.value != NO_NODE) { one.push(self.qBoxed(a, self.quoteTree(a, r.value))); }
            else { one.push(self.qBoxed(a, self.qNothing(a))); }
            return self.qVariant(a, "Return", one);
        }
        if (st.kind == StmtKind.Block) {
            return self.quoteBlock(a, a.blockStmts.get(st.at).body);
        }
        if (st.kind == StmtKind.Recover) {
            failStr(stringOf("a `recover` is not supported inside a `quote`\nnote: `ast::Node` has no form for it, nor for the `unsafe` block it has to sit in"));
        }
        none: Vec<NodeId>;
        if (st.kind == StmtKind.Break)    { return self.qVariant(a, "Break", none); }
        if (st.kind == StmtKind.Continue) { return self.qVariant(a, "Continue", none); }
        failStr(stringOf("this statement is not supported inside a `quote`\nnote: a `quote` can hold declarations, expressions, `if`, `while`, `return`, `break`, `continue` and blocks"));
        return NO_NODE;
    }
    // An `if` chain: the else is another If, a Block (the parser's always-true last link), or
    // Nothing.
    quoteIf &self inout a:Ast at:long -> NodeId {
        br: IfNode = a.ifs.get(at);
        args: Vec<NodeId>;
        args.push(self.qBoxed(a, self.quoteTree(a, br.cond)));
        args.push(self.qBoxed(a, self.quoteBlock(a, br.body)));
        if (br.elseIf < 0) { args.push(self.qBoxed(a, self.qNothing(a))); }
        else {
            nx: IfNode = a.ifs.get(br.elseIf);
            c: Expr = a.expr(nx.cond);
            always: bool = false;
            if (c.op == Op.Literal && c.kind == Lit.Bool && nx.elseIf < 0) { match c.payload { Num(v) { always = v != 0; } _ { } } }
            if (always) { args.push(self.qBoxed(a, self.quoteBlock(a, nx.body))); }
            else { args.push(self.qBoxed(a, self.quoteIf(a, br.elseIf))); }
        }
        return self.qVariant(a, "If", args);
    }
    qNothing &self inout a:Ast -> NodeId { none: Vec<NodeId>; return self.qVariant(a, "Nothing", none); }

    // One `Node.Variant(args...)` as a tree: the tag, taken from the enum's own declaration, then
    // the payload fields in order. It is the same shape `parseVariant` builds from source.
    qVariant &self inout a:Ast name:str args:Vec<NodeId> -> NodeId {
        owner: Sym = self.node;
        d: EnumDef = gReg.enumDef(gReg.findEnumSym(owner));
        vi: long = gReg.findVariant(d, name);
        if (vi < 0) { failStr(format("no variant `{}` in enum `Node`\nnote: a `quote` builds the `Node` that `stdlib::ast` declares", name)); }
        vd: VariantDef = gReg.variantAt(d, vi);
        if (vd.payloadCount != args.len()) {
            failStr(format("wrong number of values for `Node.{}`: expected {}, found {}\nnote: a `quote` builds the `Node` that `stdlib::ast` declares", name, vd.payloadCount, args.len()));
        }
        inits: Vec<InitNode>;
        inits.push(InitNode { name: intern(enumTagField()),
                              value: a.leaf(Op.Literal, Payload.Num(vd.value), d.backing) });
        for k in 0..args.len() {
            inits.push(InitNode { name: enumPayloadField(name, k), value: args.get(k) });
        }
        first: long = a.addInits(inits);
        a.lits.push(LitNode { typeName: owner, firstInit: first, initCount: inits.len(), rest: NO_NODE });
        return a.leafOf(Op.StructLit, Payload.Lit(a.lits.len() - 1), Lit.Struct, owner);
    }
    // A backed-enum constant such as `BinOp.Add`, as the integer it is.
    qEnumConst &self inout a:Ast ty:str name:str -> NodeId {
        owner: Sym = self.binOp;
        if (ty == "UnOp") { owner = self.unOp; }
        d: EnumDef = gReg.enumDef(gReg.findEnumSym(owner));
        vi: long = gReg.findVariant(d, name);
        if (vi < 0) { failStr(format("no variant `{}` in enum `{}`", name, nameOf(owner))); }
        return a.leaf(Op.Literal, Payload.Num(gReg.variantAt(d, vi).value), d.backing);
    }
    qStr &self inout a:Ast s:Sym -> NodeId { return a.leaf(Op.StringLit, Payload.Text(s), Lit.Str); }
    qInt &self inout a:Ast v:long -> NodeId { return a.leaf(Op.Literal, Payload.Num(v), Lit.Long); }
    qCall &self inout a:Ast f:str args:Vec<NodeId> -> NodeId {
        n: long = args.len();
        first: long = a.addArgs(args);
        a.calls.push(CallNode { name: intern(f), receiver: NO_NODE, firstArg: first, argCount: n,
                                       slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        return a.leaf(Op.FunctionCall, Payload.Call(a.calls.len() - 1), Lit.Int);
    }
    // `newBox(<node>)`: a child is held through a Box, which is what lets Node be recursive.
    qBoxed &self inout a:Ast node:NodeId -> NodeId {
        one: Vec<NodeId>; one.push(node);
        return self.qCall(a, "newBox", one);
    }
    qMethod &self inout a:Ast recv:NodeId m:str args:Vec<NodeId> -> NodeId {
        n: long = args.len();
        first: long = a.addArgs(args);
        a.calls.push(CallNode { name: intern(m), receiver: recv, firstArg: first, argCount: n,
                                       slot: NO_SLOT, callee: NO_NODE, sigKey: NO_SYM });
        return a.leaf(Op.MethodCall, Payload.Call(a.calls.len() - 1), Lit.Void);
    }
    // A child list has no expression form (`v.push(a); v.push(b)` are statements), so it is built
    // as a chain: `nodeList().with(a).with(b).done()`, each `with` consuming the builder. See
    // NodeList in stdlib/ast.k.
    qList &self inout a:Ast items:Vec<NodeId> -> NodeId {
        none: Vec<NodeId>;
        b: NodeId = self.qCall(a, "nodeList", none);
        for k in 0..items.len() {
            one: Vec<NodeId>; one.push(items.get(k));
            b = self.qMethod(a, b, "with", one);
        }
        empty: Vec<NodeId>;
        return self.qMethod(a, b, "done", empty);
    }
    qStrs &self inout a:Ast items:Vec<Sym> -> NodeId {
        none: Vec<NodeId>;
        b: NodeId = self.qCall(a, "nameList", none);
        for k in 0..items.len() {
            one: Vec<NodeId>; one.push(self.qStr(a, items.get(k)));
            b = self.qMethod(a, b, "with", one);
        }
        empty: Vec<NodeId>;
        return self.qMethod(a, b, "done", empty);
    }
    qName &self inout a:Ast n:Sym -> NodeId {
        one: Vec<NodeId>; one.push(self.qStr(a, n));
        return self.qVariant(a, "Name", one);
    }

    // The tree, as the expression that builds it.
    quoteTree &self inout a:Ast id:NodeId -> NodeId {
        if (id == NO_NODE) { failStr(stringOf("an empty expression cannot be quoted")); }
        e: Expr = a.expr(id);
        if (e.left != NO_NODE) {
            bn: str = binOpName(e.op);
            if (bn.len == 0) { failStr(format("this expression (`{}`) is not supported inside a `quote`", nameof(Op, e.op))); }
            args: Vec<NodeId>;
            args.push(self.qEnumConst(a, "BinOp", bn));
            args.push(self.qBoxed(a, self.quoteTree(a, e.left)));
            args.push(self.qBoxed(a, self.quoteTree(a, e.right)));
            return self.qVariant(a, "Binary", args);
        }
        un: str = unOpName(e.op);
        if (un.len > 0) {
            args: Vec<NodeId>;
            args.push(self.qEnumConst(a, "UnOp", un));
            match e.payload { Sub(v) { args.push(self.qBoxed(a, self.quoteTree(a, v))); } _ { failStr(stringOf("a malformed prefix operator cannot be quoted")); } }
            return self.qVariant(a, "Unary", args);
        }
        // `@x`: a deep copy of the Node `x` holds, so one tree may be spliced in several places.
        // Written as the method `$splice`, which the checker reads once it knows what `x` is: a
        // Node's `clone`, or, for an integer, a `bool` or a `str`, the literal holding its value
        // (`Checker.checkSplice`).
        if (e.op == Op.Splice) {
            none: Vec<NodeId>;
            match e.payload { Sub(v) { return self.qMethod(a, v, SPLICE_METHOD, none); } _ { } }
            return NO_NODE;
        }
        if (e.op == Op.AddressOf) {
            // `&x` of a variable only, for now: what a Node names is a place, not an address.
            args: Vec<NodeId>;
            args.push(self.qEnumConst(a, "UnOp", "AddrOf"));
            match e.payload {
                Sub(v) {
                    inner: Expr = a.expr(v);
                    if (inner.op != Op.Lvalue) { failStr(stringOf("`&` of anything but a variable is not supported inside a `quote` yet")); }
                    match inner.payload { Name(n) { args.push(self.qBoxed(a, self.qName(a, n))); } _ { } }
                }
                _ { failStr(stringOf("this `&` expression is not supported inside a `quote`")); }
            }
            return self.qVariant(a, "Unary", args);
        }
        if (e.op == Op.Literal) {
            // A float literal by its spelling: `Node.Float("1.5")`, where the library's Node has
            // that variant (the checker refuses the constructor where it has not).
            match e.payload {
                Text(t) {
                    fargs: Vec<NodeId>;
                    fargs.push(self.qStr(a, t));
                    return self.qVariant(a, "Float", fargs);
                }
                _ { }
            }
            if (!isInteger(e.kind) && e.kind != Lit.Bool) { failStr(stringOf("this literal is not supported inside a `quote` yet\nnote: a `quote` can hold integer, `bool`, float and string literals")); }
            args: Vec<NodeId>;
            match e.payload { Num(v) { args.push(self.qInt(a, v)); } _ { } }
            return self.qVariant(a, "Int", args);
        }
        if (e.op == Op.StringLit) {
            args: Vec<NodeId>;
            match e.payload { Text(t) { args.push(self.qStr(a, t)); } _ { } }
            return self.qVariant(a, "Str", args);
        }
        if (e.op == Op.Lvalue) {
            match e.payload { Name(n) { return self.qName(a, n); } _ { } }
        }
        if (e.op == Op.Sizeof) {
            args: Vec<NodeId>;
            t: Expr = a.measuredOf(id);
            args.push(self.qType(a, t.kind, t.structName));
            return self.qVariant(a, "Sizeof", args);
        }
        if (e.op == Op.Nameof) {
            args: Vec<NodeId>;
            args.push(self.qStr(a, e.structName));
            match e.payload { Sub(v) { args.push(self.qBoxed(a, self.quoteTree(a, v))); } _ { } }
            return self.qVariant(a, "Nameof", args);
        }
        if (e.op == Op.Cast) {
            args: Vec<NodeId>;
            match e.payload { Sub(v) { args.push(self.qBoxed(a, self.quoteTree(a, v))); } _ { } }
            args.push(self.qType(a, e.kind, e.structName));
            return self.qVariant(a, "Cast", args);
        }
        if (e.op == Op.FunctionCall || e.op == Op.MethodCall) {
            c: CallNode = a.calls.get(0);
            match e.payload { Call(i) { c = a.calls.get(i); } _ { } }
            items: Vec<NodeId>;
            for k in 0..c.argCount { items.push(self.quoteTree(a, a.argAt(c, k))); }
            args: Vec<NodeId>;
            if (e.op == Op.MethodCall) { args.push(self.qBoxed(a, self.quoteTree(a, c.receiver))); }
            args.push(self.qText(a, c.name));
            args.push(self.qList(a, items));
            if (e.op == Op.MethodCall) { return self.qVariant(a, "Method", args); }
            return self.qVariant(a, "Call", args);
        }
        if (e.op == Op.FieldAccess) {
            f: FieldNode = a.fields.get(0);
            match e.payload { Field(i) { f = a.fields.get(i); } _ { } }
            args: Vec<NodeId>;
            args.push(self.qBoxed(a, self.quoteTree(a, f.base)));
            args.push(self.qText(a, f.name));
            return self.qVariant(a, "Field", args);
        }
        if (e.op == Op.ArrayIndex) {
            ix: IndexNode = a.indexes.get(0);
            match e.payload { Index(i) { ix = a.indexes.get(i); } _ { } }
            if (ix.whole || ix.index == NO_NODE) { failStr(stringOf("a slice expression is not supported inside a `quote` yet")); }
            base: NodeId = NO_NODE;
            if (ix.base != NO_NODE) { base = self.quoteTree(a, ix.base); } else { base = self.qName(a, ix.name); }
            args: Vec<NodeId>;
            args.push(self.qBoxed(a, base));
            args.push(self.qBoxed(a, self.quoteTree(a, ix.index)));
            return self.qVariant(a, "Index", args);
        }
        if (e.op == Op.StructLit || e.op == Op.TupleLit) {
            l: LitNode = a.lits.get(0);
            match e.payload { Lit(i) { l = a.lits.get(i); } _ { } }
            if (l.rest != NO_NODE) { failStr(stringOf("a struct literal with `..rest` is not supported inside a `quote` yet")); }
            names: Vec<Sym>;
            vals: Vec<NodeId>;
            for k in 0..l.initCount {
                in: InitNode = a.inits.get(l.firstInit + k);
                names.push(in.name);
                vals.push(self.quoteTree(a, in.value));
            }
            args: Vec<NodeId>;
            if (e.op == Op.TupleLit) {
                args.push(self.qList(a, vals));
                return self.qVariant(a, "TupleLit", args);
            }
            args.push(self.qStr(a, l.typeName));
            args.push(self.qStrs(a, names));
            args.push(self.qList(a, vals));
            return self.qVariant(a, "StructLit", args);
        }
        failStr(format("this expression (`{}`) is not supported inside a `quote`", nameof(Op, e.op)));
        return NO_NODE;
    }

}
