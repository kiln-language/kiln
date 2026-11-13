// The syntax tree as text: one node per line, indented by depth, as `<kind> <detail>`.
//
// Shaped to be diffable against the C++ compiler's `--emit=ast`, so there are no positions, no
// ids, and nothing that depends on which arena slot a node happened to land in.
#include <{ast, types}>
#include <support::compiler>
#include <stdlib::{chars, fmt, string, vec}>

local indent inout out:String depth:long -> void {
    for i in 0..depth { out.pushStr("  "); }
}
local line inout out:String depth:long text:str -> void {
    indent(out, depth);
    out.pushStr(text);
    out.push('\n');
}

// The same, for a line that was built. Appending copies the bytes, so this needs no
// `unsafe` view of the String it was handed -- which is what every caller here was
// opening one for.
local lineOf inout out:String depth:long text:String -> void {
    indent(out, depth);
    out.pushString(text);
    out.push('\n');
}

// How a type is spelled in this dump, which is not how `types.k` mangles one.
//
// The mangler gives a pointer, a slice and a type variable their companion (`ptr_u8`,
// `slice_int`, `T`) because two instantiations that differ only there must not collide
// (`Vec<*int>` and `Vec<*char>` are one name under the C++ rule). That is the better rule and it
// stays. But the C++ dump prints the C++ mangling, so printing this one here reports a difference
// on every line carrying such a type and buries the tree underneath. The dump follows the C++
// spelling: the companion for a struct or a trait object, `ref_` for a borrow, a sanitized
// signature for a `fn`, the bare kind for everything else, so that what it does report is real.
local dumpType k:Lit n:Sym -> str {
    if (k == Lit.Struct || k == Lit.TraitObj) {
        if (n == NO_SYM) { return typeName(k); }
        return nameOf(n);
    }
    if (k == Lit.Ref) {
        s: String;
        s.pushStr("ref_");
        if (n != NO_SYM) { s.pushStr(nameOf(n)); }
        return keepString(s);
    }
    if (k == Lit.Fn) {
        s: String;
        s.pushStr("fn");
        if (n != NO_SYM) {
            name: str = nameOf(n);
            for i in 0..name.len {
                c: long = charAt(name, i);
                if (isAlnum(c))    { s.push(c as char); }
                else if (c == '&') { s.push('r'); }
                else               { s.push('_'); }
            }
        }
        return keepString(s);
    }
    return typeName(k);
}

// ─── expressions ─────────────────────────────────────────────────────────────

pub dumpExpr a:Ast inout out:String id:NodeId depth:long -> void {
    if (id == NO_NODE) { return; }
    e: Expr = a.expr(id);

    s: String;
    s.pushStr(opName(e.op));
    p: Payload = e.payload;
    match p {
        Num(n)   { s.push(' '); s.pushLong(n); }
        Text(t)  { s.push(' '); s.pushStr(nameOf(t)); }
        Name(n)  { s.push(' '); s.pushStr(nameOf(n)); }
        Call(c)  { s.push(' '); s.pushStr(nameOf(a.calls.get(c).name)); }
        Field(f) { s.push(' '); s.pushStr(nameOf(a.fields.get(f).name)); }
        Lit(l)   { s.push(' '); s.pushStr(nameOf(a.lits.get(l).typeName)); }
        _ { }
    }
    s.pushStr(" :");
    s.pushStr(dumpType(e.kind, e.structName));
    lineOf(out, depth, s);

    dumpExpr(a, out, e.left, depth + 1);
    dumpExpr(a, out, e.right, depth + 1);
    match p {
        Sub(v)   { dumpExpr(a, out, v, depth + 1); }
        Index(i) {
            ix: IndexNode = a.indexes.get(i);
            dumpExpr(a, out, ix.base, depth + 1);
            if (ix.whole) { line(out, depth + 1, "whole"); }
            else { dumpExpr(a, out, ix.index, depth + 1); }
        }
        Call(c) {
            cn: CallNode = a.calls.get(c);
            if (cn.receiver != NO_NODE) { dumpExpr(a, out, cn.receiver, depth + 1); }
            for k in 0..cn.argCount { dumpExpr(a, out, a.argAt(cn, k), depth + 1); }
        }
        Field(f) { dumpExpr(a, out, a.fields.get(f).base, depth + 1); }
        Lit(l) {
            ln: LitNode = a.lits.get(l);
            for k in 0..ln.initCount {
                ini: InitNode = a.inits.get(ln.firstInit + k);
                line(out, depth + 1, nameOf(ini.name));
                dumpExpr(a, out, ini.value, depth + 2);
            }
        }
        _ { }
    }
}

// ─── statements ──────────────────────────────────────────────────────────────

pub dumpBlock a:Ast inout out:String b:long depth:long -> void {
    // A function declared and not defined has no body to print.
    if (b < 0) { return; }
    line(out, depth, "block");
    n: long = a.blockLen(b);
    for k in 0..n { dumpStmt(a, out, a.stmtAt(b, k), depth + 1); }
}

pub dumpStmt a:Ast inout out:String st:Stmt depth:long -> void {
    if (st.kind == StmtKind.FunctionDef) { dumpFn(a, out, st.at, depth); return; }
    if (st.kind == StmtKind.VarDecl)     { dumpVar(a, out, st.at, depth); return; }
    if (st.kind == StmtKind.If)          { dumpIf(a, out, st.at, depth); return; }
    if (st.kind == StmtKind.While) {
        w: WhileNode = a.whiles.get(st.at);
        line(out, depth, "while");
        dumpExpr(a, out, w.cond, depth + 1);
        dumpBlock(a, out, w.body, depth + 1);
        if (w.step >= 0) { line(out, depth + 1, "step"); dumpBlock(a, out, w.step, depth + 2); }
        return;
    }
    if (st.kind == StmtKind.Loop || st.kind == StmtKind.Unsafe
        || st.kind == StmtKind.Block) {
        bs: BlockStmtNode = a.blockStmts.get(st.at);
        if (st.kind == StmtKind.Loop) { line(out, depth, "loop"); }
        else if (st.kind == StmtKind.Unsafe) { line(out, depth, "unsafe"); }
        dumpBlock(a, out, bs.body, depth + 1);
        return;
    }
    if (st.kind == StmtKind.Return) {
        r: ReturnNode = a.returns.get(st.at);
        line(out, depth, "return");
        dumpExpr(a, out, r.value, depth + 1);
        return;
    }
    if (st.kind == StmtKind.Match) {
        m: MatchNode = a.matches.get(st.at);
        s: String;
        s.pushStr("match ");
        s.pushStr(nameOf(m.scrutinee));
        lineOf(out, depth, s);
        for k in 0..m.armCount {
            arm: ArmNode = a.arms.get(m.firstArm + k);
            t: String;
            t.pushStr("arm ");
            if (arm.variant == NO_SYM) { t.push('_'); } else { t.pushStr(nameOf(arm.variant)); }
            for j in 0..arm.bindCount {
                t.push(' ');
                t.pushStr(nameOf(a.names.get(arm.firstBind + j)));
            }
            lineOf(out, depth + 1, t);
            dumpBlock(a, out, arm.body, depth + 2);
        }
        return;
    }
    if (st.kind == StmtKind.StructDecl) {
        s: String;
        s.pushStr("struct ");
        s.pushStr(nameOf(a.structDecls.get(st.at)));
        lineOf(out, depth, s);
        return;
    }
    if (st.kind == StmtKind.Break)    { line(out, depth, "break"); return; }
    if (st.kind == StmtKind.Continue) { line(out, depth, "continue"); return; }
    if (st.kind == StmtKind.Expr) {
        es: ExprStmtNode = a.exprStmts.get(st.at);
        line(out, depth, "expr");
        dumpExpr(a, out, es.value, depth + 1);
        return;
    }
    line(out, depth, "?stmt");
}

local dumpFn a:Ast inout out:String at:long depth:long -> void {
    f: FnNode = a.fns.get(at);
    s: String;
    s.pushStr("fn ");
    s.pushStr(nameOf(f.name));
    s.pushStr(" -> ");
    s.pushStr(dumpType(f.returnKind, f.returnStruct));
    lineOf(out, depth, s);
    for k in 0..f.argCount { dumpDecl(out, a.paramAt(f, k), depth + 1, "param"); }
    dumpBlock(a, out, f.body, depth + 1);
}

local dumpVar a:Ast inout out:String at:long depth:long -> void {
    d: VarDeclNode = a.decls.get(at);
    dumpDecl(out, d, depth, "var");
    if (d.init != NO_NODE) { dumpExpr(a, out, d.init, depth + 1); }
}

local dumpDecl inout out:String d:VarDeclNode depth:long what:str -> void {
    s: String;
    s.pushStr(what);
    s.push(' ');
    s.pushStr(nameOf(d.name));
    s.pushStr(" :");
    s.pushStr(dumpType(d.kind, d.structName));
    if (d.isArray) {
        s.pushStr(" [");
        // Inside a template the length may still be its parameter: `[N]`, not a negative number.
        if (isParamCount(d.count)) { s.pushStr(nameOf(paramOfCount(d.count))); } else { s.pushLong(d.count); }
        s.push(']');
    }
    lineOf(out, depth, s);
}

local dumpIf a:Ast inout out:String at:long depth:long -> void {
    n: IfNode = a.ifs.get(at);
    line(out, depth, "if");
    dumpExpr(a, out, n.cond, depth + 1);
    dumpBlock(a, out, n.body, depth + 1);
    if (n.elseIf >= 0) { dumpIf(a, out, n.elseIf, depth); }
}

// The spelling `--emit=ast` prints for an operator. Not the variant's name (`nameof` would give
// `LessThan`, and the dump has to read `<` to diff against the C++ compiler's), so it is data.
// Keyed by the member rather than laid out in the enum's order: the table used to be a `vec![]`
// whose entries lined up with `Op` by position and were tied to it only by a trailing comment, so
// inserting a variant anywhere but the end silently relabelled every operator after it. Nothing
// checked that, and `--emit=ast` is what the parser is diffed against.
//
// Seeded with `?`, which is what an operator added to `Op` and forgotten here prints as. The same
// shape `irOpNames` in codegen/irdump.k already used.
local gOpNames: Vec<str> = opNames();

local opNames -> Vec<str> {
    t: Vec<str>;
    i: long = 0;
    while (i <= (Op.ArrayLit as long)) { t.push("?"); i = i + 1; }
    t.set(Op.Assignment       as long, "=");
    t.set(Op.Addition         as long, "+");
    t.set(Op.Subtraction      as long, "-");
    t.set(Op.Multiplication   as long, "*");
    t.set(Op.Division         as long, "/");
    t.set(Op.Modulus          as long, "%");
    t.set(Op.LessThan         as long, "<");
    t.set(Op.GreaterThan      as long, ">");
    t.set(Op.IsLessOrEqual    as long, "<=");
    t.set(Op.IsGreaterOrEqual as long, ">=");
    t.set(Op.IsEqual          as long, "==");
    t.set(Op.IsNotEqual       as long, "!=");
    t.set(Op.BitwiseAnd       as long, "&");
    t.set(Op.BitwiseOr        as long, "|");
    t.set(Op.BitwiseXor       as long, "^");
    t.set(Op.ShiftLeft        as long, "<<");
    t.set(Op.ShiftRight       as long, ">>");
    t.set(Op.LogicalAnd       as long, "&&");
    t.set(Op.LogicalOr        as long, "||");
    t.set(Op.BitwiseNot       as long, "~");
    t.set(Op.LogicalNot       as long, "!");
    t.set(Op.FunctionCall     as long, "call");
    t.set(Op.Lvalue           as long, "lvalue");
    t.set(Op.ArrayIndex       as long, "index");
    t.set(Op.Cast             as long, "cast");
    t.set(Op.AddressOf        as long, "addrof");
    t.set(Op.StringLit        as long, "str");
    t.set(Op.TupleLit         as long, "tuple");
    t.set(Op.FieldAccess      as long, "field");
    t.set(Op.StructLit        as long, "structlit");
    t.set(Op.MethodCall       as long, "method");
    t.set(Op.Sizeof           as long, "sizeof");
    t.set(Op.Nameof           as long, "nameof");
    t.set(Op.Splice           as long, "splice");
    t.set(Op.MacroCall        as long, "macro");
    t.set(Op.Deref            as long, "deref");
    t.set(Op.Literal          as long, "lit");
    t.set(Op.Image            as long, "image");
    t.set(Op.MakeTraitObj     as long, "lit");
    t.set(Op.ArrayLit         as long, "array");
    return t;
}

pub opName op:Op -> str {
    i: long = op as long;
    if (i < 0 || i >= gOpNames.len()) { return "lit"; }
    return gOpNames.get(i);
}
