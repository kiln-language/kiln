// What an error says besides its message, and how it names a type.
//
// Every diagnostic goes through `fail` (`support::compiler`), which sits below the registry and
// cannot read it. The two hooks installed here (`installDiagnostics`) are how it reaches what only
// the registry knows:
//
//   - A type is named the way it is written: `Option<long>`, `Buf<FileOut, 8>`, `&Res`, and `Expr`
//     rather than `parse::ast::Expr` when no other declared type has that name. Messages are
//     assembled from mangled names all over the compiler (`option::Option_long`), so rather than
//     have every message site spell its types, the message is rewritten on its way out. Every
//     `::`-qualified word that names a type (an instance, a struct, an enum, a trait, or a borrow
//     or pointer of one) is replaced by its spelling, and `T_method` by `T.method`.
//   - An error inside a generic instance or a derive adds a note for each link of the chain back
//     to code nothing stamped, in clang's form:
//     `app.k:12:5: note: in instantiation of `Vec<String>` requested here`.
//   - An internal compiler error adds a note saying what the compiler was doing.
//
// Only an error pays for any of this.
#include <{registry, types}>
#include <support::compiler>
#include <stdlib::{chars, file, io, option, string, vec}>

// How far an "instantiated from" chain is followed. A real chain is two or three links; this only
// bounds a cycle the tables should not have.
local MAX_NOTE_DEPTH: long = 8;
// The instance the last error's chain began at: a second error in the same instance does not
// print the same chain again.
local var gLastChain: Sym = NO_SYM;

// The registry, as this file reads it: through its address, taken once at startup, and never by
// name. Everything here runs on an error's way out (`fail` calls the two hooks), and an error can
// be raised inside a registry method while that method holds `gReg` lent. Naming `gReg` here would
// read it, and the index `bareIfUnique` brings up to date would write it, in the middle of the
// lend, which the law of exclusivity refuses. Through the address that is still sound, because
// `fail` never returns: the method holding the lend never runs again once a hook has, so nothing it
// keeps of the registry can go stale.
local var gRegAt: *Registry;

pub installDiagnostics -> void {
    unsafe { gRegAt = &gReg as *Registry; }
    gSpellHook = &spellMessage;
    gNoteHook = &diagNotes;
}

// ─── what to include ─────────────────────────────────────────────────────────

// A name nothing declares that the standard library has a module named after (`Result`,
// `stdlib::result`): a `help:` line saying what to include, to go at the end of the message, or
// "". Only an error pays for the file lookup.
pub stdlibHint bare:str -> str {
    if (bare.len == 0) { return ""; }
    s: String;
    for i in 0..bare.len {
        c: long = charAt(bare, i);
        if (c >= 'A' as long && c <= 'Z' as long) { c = c + 32; }
        s.push(c as char);
    }
    mod: str = keepString(s);
    path: String;
    path.pushStr(STDLIB_ROOT);
    path.push('/');
    path.pushStr(mod);
    path.pushStr(".k");
    if (!fileExists(keepString(path))) { return ""; }
    return keepString(format("\nhelp: the standard library has a module named `{}`: `#include <{}::{}>`", mod, STDLIB_PKG, mod));
}

// ─── a type, as written ──────────────────────────────────────────────────────

// A declared type's name as the reader would write it: bare when no other declared type has the
// same last component, qualified otherwise.
local bareIfUnique n:str -> str {
    bare: str = lastComponentOf(n);
    if (bare.len == n.len) { return n; }
    unsafe {
        gRegAt.indexLastComponents();
        i: long = gRegAt.byBare.firstOf(bare);
        while (i >= 0) {
            // An instance's mangled name ends in its last argument's (`vec::Vec_string::String`,
            // a trait's `Iter_geo::P`): it is not another declaration of the name.
            q: str = nameOf(gRegAt.byBare.qualAt(i));
            if (q != n && gRegAt.findRequest(q) < 0 && gRegAt.traitInstOf(gRegAt.byBare.qualAt(i)) < 0) { return n; }
            i = gRegAt.byBare.nextOf(i);
        }
    }
    return bare;
}

// Whether `n` names a type this program declares or stamped. A generic function's template (a
// method with type parameters of its own, `L_pick`) is recorded beside the types' and is not one.
local namesDeclaredType n:str -> bool {
    unsafe {
        if (gRegAt.findStruct(n) >= 0 || gRegAt.findEnum(n) >= 0 || gRegAt.findTrait(n) >= 0
            || gRegAt.findRequest(n) >= 0) { return true; }
        at: long = gRegAt.findTemplate(n);
        if (at < 0) { return false; }
        t: GTemplate = gRegAt.templateDef(at);
        return t.fieldCount > 0 || t.isEnum;
    }
}

// A type a method may belong to: a declared one, or a scalar (`methods long for Ord`).
local namesOwner n:str -> bool {
    return namesDeclaredType(n) || namesScalar(n);
}

// One type argument, or anything else a `TypeRef` holds.
pub spellTypeRef t:TypeRef -> String {
    out: String;
    if (t.base == Lit.Len) { out.pushStr(nameOf(t.name)); return out; }
    if (t.name == NO_SYM) { out.pushStr(typeName(t.base)); return out; }
    if (t.base == Lit.Ref)   { out.push('&'); out.pushString(spellTypeName(nameOf(t.name))); return out; }
    if (t.base == Lit.Ptr)   { out.push('*'); out.pushString(spellTypeName(nameOf(t.name))); return out; }
    if (t.base == Lit.Slice) { out.push('['); out.pushString(spellTypeName(nameOf(t.name))); out.push(']'); return out; }
    if (t.base == Lit.Fn)    { out.pushStr(nameOf(t.name)); return out; }   // the key is spelled `fn(..)->R`
    out.pushString(spellTypeName(nameOf(t.name)));
    return out;
}

// A type's name (as the compiler holds it: qualified, mangled for an instance) as it is written.
pub spellTypeName n:str -> String {
    return spellTypeDepth(n, 0);
}

local spellTypeDepth n:str depth:long -> String {
    out: String;
    if (depth > MAX_NOTE_DEPTH || namesScalar(n)) { out.pushStr(n); return out; }
    unsafe {
        // A closure's capture struct is named by the compiler, not the author.
        if (gRegAt.isClosureEnv(symIfAny(n))) { out.pushStr("closure"); return out; }
        // A borrow, a pointer or a slice of one, spelled as the mangler wrote them.
        if (strStartsWith(n, "ref_") && namesDeclaredType(strSlice(n, 4, n.len - 4))) {
            out.push('&'); out.pushString(spellTypeDepth(strSlice(n, 4, n.len - 4), depth + 1)); return out;
        }
        if (strStartsWith(n, "ptr_") && namesDeclaredType(strSlice(n, 4, n.len - 4))) {
            out.push('*'); out.pushString(spellTypeDepth(strSlice(n, 4, n.len - 4), depth + 1)); return out;
        }
        if (strStartsWith(n, "slice_") && namesDeclaredType(strSlice(n, 6, n.len - 6))) {
            out.push('['); out.pushString(spellTypeDepth(strSlice(n, 6, n.len - 6), depth + 1)); out.push(']'); return out;
        }
        // A tuple is its elements.
        if (isTupleName(intern(n)) && gRegAt.findStruct(n) >= 0) {
            d: StructDef = gRegAt.structDef(gRegAt.findStruct(n));
            out.push('(');
            for k in 0..d.fieldCount {
                if (k > 0) { out.pushStr(", "); }
                f: FieldDef = gRegAt.fieldAt(d, k);
                out.pushString(spellTypeRef(TypeRef { base: f.kind, name: f.structName }));
            }
            out.push(')');
            return out;
        }
        // An instance: its template, then its arguments.
        r: long = gRegAt.findRequest(n);
        if (r >= 0) {
            req: GRequest = gRegAt.requestAt(r);
            out.pushStr(bareIfUnique(nameOf(req.base)));
            out.push('<');
            for k in 0..req.argCount {
                if (k > 0) { out.pushStr(", "); }
                out.pushString(spellTypeRef(gRegAt.gArgAt(req, k)));
            }
            out.push('>');
            return out;
        }
        // A trait instance (`Iter_long`): its trait, then its arguments.
        ti: long = gRegAt.traitInstOf(symIfAny(n));
        if (ti >= 0) {
            tr: TraitRef = gRegAt.traitInstRef(ti);
            out.pushStr(bareIfUnique(nameOf(tr.name)));
            out.push('<');
            for k in 0..tr.argCount {
                if (k > 0) { out.pushStr(", "); }
                out.pushString(spellTypeRef(gRegAt.traitArgAt(tr, k)));
            }
            out.push('>');
            return out;
        }
    }
    if (namesDeclaredType(n)) { out.pushStr(bareIfUnique(n)); return out; }
    out.pushStr(n);
    return out;
}

// ─── a message, as written ───────────────────────────────────────────────────

local isWordByte c:long -> bool { return isAlnum(c) || c == '_' || c == '$'; }

// One `::`-qualified word of a message: the type it names, spelled, or `T.method` for a method
// symbol `T_method` whose `T` is a type. Anything else (a function, a global, a module) as it is.
local spellWord w:str -> String {
    if (namesDeclaredType(w)) { return spellTypeName(w); }
    if (strStartsWith(w, "ref_") || strStartsWith(w, "ptr_") || strStartsWith(w, "slice_")) {
        s: String = spellTypeName(w);
        unsafe { if (s.view() != w) { return s; } }
    }
    // `T_method`: the longest `T` that names a type, the rest a plain name.
    i: long = w.len - 1;
    while (i > 0) {
        if (charAt(w, i) == '_') {
            head: str = strSlice(w, 0, i);
            tail: str = strSlice(w, i + 1, w.len - i - 1);
            if (tail.len > 0 && strFind(tail, "::").isNone() && namesDeclaredType(head)) {
                out: String = spellTypeName(head);
                out.push('.');
                out.pushStr(tail);
                return out;
            }
        }
        i = i - 1;
    }
    // `T_Trait_method`: a method whose name carries its trait (`implFnName`: a file's own trait,
    // `long_geo::Ord_cmp`, or one with arguments, `Meters_Eq_Feet_eq`), spelled `T.method`.
    j: long = 1;
    while (j < w.len) {
        if (charAt(w, j) == '_' && namesOwner(strSlice(w, 0, j))) {
            rest: str = strSlice(w, j + 1, w.len - j - 1);
            k: long = rest.len - 1;
            while (k > 0 && charAt(rest, k) != '_') { k = k - 1; }
            if (k > 0) {
                method: str = strSlice(rest, k + 1, rest.len - k - 1);
                if (method.len > 0 && strFind(method, "::").isNone() && regTrait(strSlice(rest, 0, k)) >= 0) {
                    out: String = spellTypeName(strSlice(w, 0, j));
                    out.push('.');
                    out.pushStr(method);
                    return out;
                }
            }
        }
        j = j + 1;
    }
    // A generic function, by its own name (`fixedOf`).
    if (regTemplate(w) >= 0) { return stringOf(lastComponentOf(w)); }
    return stringOf(w);
}

// `long_cmp`, a scalar's method from an implementation (a scalar's name belongs to no module, so
// the word is not qualified and `spellWord` never sees it): `long.cmp`. Anything else as it is.
local spellScalarMethod w:str -> String {
    cut: long = 0;
    while (cut < w.len && charAt(w, cut) != '_') { cut = cut + 1; }
    if (cut == 0 || cut + 1 >= w.len || !namesScalar(strSlice(w, 0, cut))) { return stringOf(w); }
    owner: Sym = intern(strSlice(w, 0, cut));
    unsafe {
        for i in 0..gRegAt.implCount() {
            im: TraitImplDef = gRegAt.implAt(i);
            if (im.structName != owner) { continue; }
            for k in 0..im.fnCount {
                if (nameOf(gRegAt.implFnAt(im, k)) == w) {
                    out: String = stringOf(strSlice(w, 0, cut));
                    out.push('.');
                    out.pushStr(strSlice(w, cut + 1, w.len - cut - 1));
                    return out;
                }
            }
        }
    }
    return stringOf(w);
}

local hasDollar w:str -> bool {
    for k in 0..w.len { if (charAt(w, k) == '$') { return true; } }
    return false;
}
local allDigits s:str -> bool {
    if (s.len == 0) { return false; }
    for k in 0..s.len { if (!isDigit(charAt(s, k))) { return false; } }
    return true;
}

// `s` is `prefix` followed by a number.
local numbered s:str prefix:str -> bool {
    return strStartsWith(s, prefix) && allDigits(strSlice(s, prefix.len, s.len - prefix.len));
}

// A name the compiler made, as the source would say it (every message passes through here, so a
// path a phase prints from its own tables reads as written): a local renamed for shadowing
// (`x$2`) by its name, a variant's payload slot (`$Call$0`) as `Call.0`, a tuple's element (`$1`)
// as `1`, a hidden local by what it holds. Anything else with a `$` (a tuple type's mangled name,
// a link alias) is left to the rest of the spelling.
local spellInternal w:str -> str {
    d: long = 0;
    while (d < w.len && charAt(w, d) != '$') { d = d + 1; }
    rest: str = strSlice(w, d + 1, w.len - d - 1);
    if (d > 0) {
        if (allDigits(rest)) { return strSlice(w, 0, d); }
        return w;
    }
    if (allDigits(rest)) { return rest; }
    if (numbered(rest, "bmatch") || numbered(rest, "match") || numbered(rest, "try")) { return "the value being matched"; }
    if (numbered(rest, "fors") || numbered(rest, "forp")) { return "the collection the loop walks"; }
    e: long = 0;
    while (e < rest.len && charAt(rest, e) != '$') { e = e + 1; }
    if (e > 0 && e < rest.len && isUpper(charAt(rest, 0)) && allDigits(strSlice(rest, e + 1, rest.len - e - 1))) {
        s: String;
        s.pushStr(strSlice(rest, 0, e));
        s.push('.');
        s.pushStr(strSlice(rest, e + 1, rest.len - e - 1));
        return keepString(s);
    }
    return w;
}

pub spellMessage msg:str -> String {
    out: String;
    i: long = 0;
    while (i < msg.len) {
        c: long = charAt(msg, i);
        if (!isWordByte(c)) { out.push(c as char); i = i + 1; continue; }
        // A word: letters, digits, `_`, `$`, and `::` between them.
        j: long = i;
        qualified: bool = false;
        while (j < msg.len) {
            d: long = charAt(msg, j);
            if (isWordByte(d)) { j = j + 1; continue; }
            if (d == ':' && j + 2 < msg.len && charAt(msg, j + 1) == ':' && isWordByte(charAt(msg, j + 2))) {
                qualified = true;
                j = j + 2;
                continue;
            }
            break;
        }
        w: str = strSlice(msg, i, j - i);
        if (qualified) { out.pushString(spellWord(w)); }
        else if (hasDollar(w)) { out.pushStr(spellInternal(w)); }
        else if (regTraitInst(symIfAny(w)) >= 0) { out.pushString(spellTypeName(w)); }
        else { out.pushString(spellScalarMethod(w)); }
        i = j;
    }
    return out;
}

// ─── the notes ───────────────────────────────────────────────────────────────

local positionText p:long -> String {
    out: String;
    f: Sym = posFile(p);
    if (f == NO_SYM) { out.pushStr("<input>"); } else { out.pushStr(nameOf(f)); }
    out.push(':');
    out.pushLong(posLine(p));
    out.push(':');
    out.pushLong(posCol(p));
    return out;
}

// What an instance is called in a note: a type instance spelled, a function instance or a derive
// by the label it was recorded with.
local instanceText inst:Sym -> String {
    o: Origin = originOf(inst);
    if (o.label != NO_SYM) { return spellMessage(nameOf(o.label)); }
    return spellTypeName(nameOf(inst));
}

local diagNotes msg:str -> void {
    // An internal compiler error: say so, and what the compiler was doing. The source line it was
    // at has already been shown under the error.
    if (strStartsWith(msg, "internal compiler error")) {
        what: String;
        what.pushStr("this is a bug in the compiler");
        if (gPhase.len > 0) { what.pushStr(", hit while "); what.pushStr(gPhase); }
        if (gCtxFn != NO_SYM) { what.pushStr(" `"); what.pushString(spellWord(nameOf(gCtxFn))); what.pushStr("`"); }
        eprintln("note: {}", what);
    }
    // Inside a generic instance or a derive: where it was asked for, back to code nothing stamped.
    inst: Sym = gCtxInst;
    if (inst == NO_SYM) { inst = fnOwnerOf(gCtxFn); }
    if (inst == NO_SYM) { gLastChain = NO_SYM; return; }
    if (inst == gLastChain) { eprintln("note: in the same instantiation as the previous error"); return; }
    gLastChain = inst;
    seen: Vec<Sym>;
    depth: long = 0;
    while (inst != NO_SYM && depth < MAX_NOTE_DEPTH) {
        for k in 0..seen.len() { if (seen.get(k) == inst) { return; } }
        seen.push(inst);
        o: Origin = originOf(inst);
        // An instance a field of its parent asked for was asked for where the parent was: one
        // note says both (`Inner<long>, inside Outer<long>`).
        what: String = instanceText(inst);
        while (o.parent != NO_SYM && o.pos != 0 && originOf(o.parent).pos == o.pos && depth < MAX_NOTE_DEPTH) {
            what.pushStr(", inside ");
            what.pushString(instanceText(o.parent));
            seen.push(o.parent);
            o = originOf(o.parent);
            depth = depth + 1;
        }
        if (o.pos == 0) { eprintln("note: in instantiation of `{}`", what); }
        else { eprintln("{}: note: in instantiation of `{}` requested here", positionText(o.pos), what); }
        inst = o.parent;
        depth = depth + 1;
    }
    if (inst != NO_SYM) { eprintln("note: (further instantiation context omitted)"); }
}

// One lookup each in the registry, through its address (`gRegAt`).
local regTrait q:str -> long { unsafe { return gRegAt.findTrait(q); } }
local regTemplate q:str -> long { unsafe { return gRegAt.findTemplate(q); } }
local regTraitInst n:Sym -> long { unsafe { return gRegAt.traitInstOf(n); } }
