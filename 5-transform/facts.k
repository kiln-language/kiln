// The facts table: what a package's own compile decided about it that its dependents would
// otherwise have to re-derive from its bodies -- which they do not check.
//
// Per source function: its parameters' final conventions and representations (a read-only
// struct parameter is a borrow, which is the call ABI), its return type as settled (a closure
// written without `-> T`), whether it never returns, which by-reference parameters it writes
// through, and the trait dispatches it hands a parameter to (whose answer depends on every
// implementation in the final program, so a dependent re-asks it). Per global: what the
// evaluator folded it to, as bytes with their pointers named, so a dependent's compile-time code
// can read it. And the globals a startup initializer of this package (or one below it) may write,
// which a dependent's fold must not trust.
//
// A function's facts are found by its index in the tree (`fnFactOf`): a `.klib` lists them per
// module, in the order of the module's function nodes, and the reader files each under the index
// that node got (`1-cumulation/KlibTree.k`). A global's are found by its qualified name, which is
// unique and which the evaluator asks by. The encoding is the `.klib`'s; this is only the table.
#include <support::compiler>
#include <parse::{ast, registry}>
#include <stdlib::{chars, map, option, string, vec}>

// A `&self` method called, in a `match` arm through a borrow, on the place whose payload the arm
// holds. The checker notes it (`bmArmArg`); the guard refuses it only if the method writes `self`
// (`ConstGuard.holdSelfLends`), which its write masks decide once every body is settled.
// `callee` is the method's function, `pos` where the call stands, `what` the place, `made` the
// binding the arm holds.
pub struct SelfLend { callee: long, pos: long, fnName: Sym, what: str, made: Sym }
pub var gSelfLends: Vec<SelfLend>;

// The functions that never return, by name, as the settled program decided (`checkReturns`): the
// lowerer marks a call to one `noReturn`, so the back end knows no path leaves it.
pub var gNoReturnFns: HashMap<str, bool> = map![];

// A `match` arm holding a borrow into a `var` global's payload (`match &G.f { Some(r) { ... } }`).
// The checker refuses a write to the global the arm itself makes; one a function the arm calls
// makes, by naming the global, is the guard's to find (`ConstGuard.holdArms`), once it knows what
// every function writes. `body` is the arm's block, `pos` where the match stands.
pub struct HeldArm { body: long, global: Sym, pos: long, fnName: Sym, made: Sym }
pub var gHeldArms: Vec<HeldArm>;

// Every function whose address the checked code takes (`&f`): what a call through a fn value may
// reach, for the guard's question of which globals such a call writes.
pub var gAddressedFns: Vec<Sym>;

pub struct ParamFact { conv: Conv, kind: Lit }
// `param` of the function is handed, through calls, to position `pos` of a dispatch through
// `trait`'s method `slot`.
pub struct DepFact { param: long, trait: Sym, slot: long, pos: long }
pub struct FnFact {
    divergent: bool,
    writes: long,                    // the guard's mask: bit k = writes through parameter k
    retKind: Lit, retStruct: Sym,
    firstParam: long, paramCount: long,
    firstDep: long, depCount: long
}
// What a global folded to: nothing (it initializes at startup), zero bytes (no initializer), a
// scalar, or an image.
pub enum GlobalState: int { Startup, Zero, Scalar, Image }
pub struct GlobalFact { name: Sym, state: GlobalState, value: long, image: long }
pub struct ImgFact { firstByte: long, byteCount: long, firstReloc: long, relocCount: long, isBlock: bool }
// A relocation inside an image. `image` indexes this table (a block); `concrete`/`trait` say
// which vtable a Vtable relocation names, which its label alone cannot be split back into.
pub struct RelocFact { offset: long, kind: RelocKind, target: Sym, image: long, delta: long,
                       concrete: Sym, trait: Sym }

pub struct Facts {
    fns: Vec<FnFact>,
    params: Vec<ParamFact>,
    deps: Vec<DepFact>,
    globals: Vec<GlobalFact>,
    globalAt: HashMap<str, long>,
    images: Vec<ImgFact>,
    bytes: Vec<u8>,
    relocs: Vec<RelocFact>,
    poisonAll: bool,
    poison: Vec<Sym>,
    poisonAt: HashMap<str, bool>
}

methods Facts for Default {
    new -> Facts {
        return Facts { fns: vec![], params: vec![], deps: vec![],
                       globals: vec![], globalAt: map![], images: vec![], bytes: vec![],
                       relocs: vec![], poisonAll: false, poison: vec![], poisonAt: map![] };
    }
}

// Everything the dependencies' `.klib`s said, merged: what a compile reads.
pub var gFacts: Facts;
// What this package's compile decided about itself: what it writes.
pub var gOutFacts: Facts;

// Per function of the tree, by its index: its facts in `gFacts`, or -1 (a function this compile
// owns, or one its package recorded nothing for). Filled as a `.klib`'s modules are loaded.
pub var gFnFact: Vec<long> = vec![];
// Writing: per function of the tree, its facts in `gOutFacts`, or -1.
pub var gOutFnFactAt: Vec<long> = vec![];

pub fnFactOf i:long -> long {
    if (i < 0 || i >= gFnFact.len()) { return -1; }
    return gFnFact.get(i);
}
pub noteFnFact i:long fact:long -> void {
    while (gFnFact.len() <= i) { gFnFact.push(-1); }
    gFnFact.set(i, fact);
}

// ─── instance functions other packages compiled ──────────────────────────────

// One instance function (a method of `Vec<long>`, `vecOf<long>`) a loaded `.klib` compiled and
// exports: its name, the alias it is linked by, what it was compiled against (the fingerprint,
// `Mono.fingerprint`), its facts in `gFacts`, and which `.klib` (`gKlibRank` orders them).
// Chained by name, in load order.
pub struct InstExport { name: Sym, alias: Sym, fp: long, fact: long, klib: long, next: long }
pub var gInstExports: Vec<InstExport> = vec![];
pub var gInstExportAt: HashMap<str, long> = map![];
// Per loaded `.klib`, its place in dependency order (each after what it depends on).
pub var gKlibRank: Vec<long> = vec![];

pub addInstExport e:InstExport -> void {
    at: long = gInstExports.len();
    gInstExports.push(e);
    head: long = gInstExportAt.getOr(nameOf(e.name), -1);
    if (head < 0) { gInstExportAt.put(nameOf(e.name), at); return; }
    while (gInstExports.get(head).next >= 0) { head = gInstExports.get(head).next; }
    prev: InstExport = gInstExports.get(head);
    prev.next = at;
    gInstExports.set(head, prev);
}

// The export a dependent links `name` to: of the `.klib`s that compiled it against what this
// compile sees (`fp`), the first in dependency order. -1 when there is none, and it is stamped here.
pub instExportFor name:Sym fp:long -> long {
    best: long = -1;
    i: long = gInstExportAt.getOr(nameOf(name), -1);
    while (i >= 0) {
        e: InstExport = gInstExports.get(i);
        if (e.fp == fp && (best < 0 || klibRank(e.klib) < klibRank(gInstExports.get(best).klib))) { best = i; }
        i = e.next;
    }
    return best;
}
local klibRank k:long -> long {
    if (k < 0 || k >= gKlibRank.len()) { return k; }
    return gKlibRank.get(k);
}

// Writing: this package's own instance functions, by name, to their facts in `gOutFacts`.
pub var gOutInstFact: HashMap<str, long> = map![];

// The label of a vtable an image points at, back to the pair it was made from. Filled where the
// evaluator promotes a trait object, read where the facts are written.
pub var gVtablePairs: HashMap<str, long> = map![];
pub var gVtableConcrete: Vec<Sym> = vec![];
pub var gVtableTrait: Vec<Sym> = vec![];

pub noteVtablePair label:str concrete:Sym trait:Sym -> void {
    if (gVtablePairs.has(label)) { return; }
    gVtablePairs.put(label, gVtableConcrete.len());
    gVtableConcrete.push(concrete);
    gVtableTrait.push(trait);
}

// A cursor over a metadata text (its methods are at the end of this file).
pub struct MetaIn { text: str, pos: long, origin: str }

methods Facts {
    globalFact &self name:Sym -> long {
        hit: Option<long> = self.globalAt.find(nameOf(name));
        match hit { Some(i) { return i; } None { } }
        return -1;
    }
    paramAt &self f:FnFact k:long -> ParamFact { return self.params.get(f.firstParam + k); }
    depAt &self f:FnFact k:long -> DepFact { return self.deps.get(f.firstDep + k); }

    // Answers the new entry's index.
    addFn &self f:FnFact ps:Vec<ParamFact> ds:Vec<DepFact> -> long {
        first: long = self.params.len();
        self.params.extend(ps);
        firstDep: long = self.deps.len();
        self.deps.extend(ds);
        self.fns.push(FnFact { divergent: f.divergent, writes: f.writes,
                               retKind: f.retKind, retStruct: f.retStruct,
                               firstParam: first, paramCount: ps.len(),
                               firstDep: firstDep, depCount: ds.len() });
        return self.fns.len() - 1;
    }
    addGlobal &self g:GlobalFact -> void {
        self.globalAt.put(nameOf(g.name), self.globals.len());
        self.globals.push(g);
    }
    addPoison &self g:Sym -> void {
        if (self.poisonAt.has(nameOf(g))) { return; }
        self.poisonAt.put(nameOf(g), true);
        self.poison.push(g);
    }
}

// ─── the header's text ───────────────────────────────────────────────────────

// A name as `<length>:<bytes>`, or `-` for none: a name may hold anything a signature's spelling
// or a string literal does, spaces included, and this way nothing has to be escaped.
pub putName inout s:String n:Sym -> void {
    if (n == NO_SYM) { s.push('-'); return; }
    putText(s, nameOf(n));
}
pub putText inout s:String t:str -> void {
    s.pushLong(t.len);
    s.push(':');
    s.pushStr(t);
}


// A cursor over a metadata text. A malformed record stops the compiler with what it was reading:
// the input was written by this compiler, so a mismatch means a damaged or foreign file, and the
// version line has already refused a foreign one.

pub metaIn text:str origin:str -> MetaIn { return MetaIn { text: text, pos: 0, origin: origin }; }

methods MetaIn {
    atEnd &self -> bool {
        self.skipBlank();
        return self.pos >= self.text.len;
    }
    skipBlank &self -> void {
        while (self.pos < self.text.len) {
            c: long = charAt(self.text, self.pos);
            if (c != ' ' && c != '\n') { return; }
            self.pos = self.pos + 1;
        }
    }
    word &self -> str {
        self.skipBlank();
        start: long = self.pos;
        while (self.pos < self.text.len) {
            c: long = charAt(self.text, self.pos);
            if (c == ' ' || c == '\n') { return strSlice(self.text, start, self.pos - start); }
            self.pos = self.pos + 1;
        }
        return strSlice(self.text, start, self.pos - start);
    }
    num &self -> long {
        w: str = self.word();
        got: Option<long> = parseLong(w);
        match got { Some(v) { return v; } None { } }
        self.bad(format("a number, found '{}'", w));
        return 0;
    }
    // `<length>:<bytes>` back to an interned name; `-` is none.
    name &self -> Sym {
        self.skipBlank();
        // A prefixed name starts with its length, so a dash can only be the absence of one.
        if (charAt(self.text, self.pos) == '-') { self.pos = self.pos + 1; return NO_SYM; }
        return intern(self.text0());
    }
    // `<length>:<bytes>` as text that lives as long as the metadata does.
    text0 &self -> str {
        self.skipBlank();
        n: long = 0;
        while (self.pos < self.text.len && isDigit(charAt(self.text, self.pos))) {
            n = n * 10 + charAt(self.text, self.pos) - '0';
            self.pos = self.pos + 1;
        }
        if (charAt(self.text, self.pos) != ':' || self.pos + 1 + n > self.text.len) {
            self.bad(stringOf("a length-prefixed name"));
        }
        self.pos = self.pos + 1;
        out: str = strSlice(self.text, self.pos, n);
        self.pos = self.pos + n;
        return out;
    }
    // The rest of the current line, without its newline.
    restOfLine &self -> str {
        start: long = self.pos;
        while (self.pos < self.text.len && charAt(self.text, self.pos) != '\n') { self.pos = self.pos + 1; }
        out: str = strSlice(self.text, start, self.pos - start);
        if (self.pos < self.text.len) { self.pos = self.pos + 1; }
        return out;
    }
    // `n` raw bytes starting right after the current line's newline -- a blob.
    blob &self n:long -> str {
        if (self.pos < self.text.len && charAt(self.text, self.pos) == '\n') { self.pos = self.pos + 1; }
        if (self.pos + n > self.text.len) { self.bad(stringOf("a blob running past the end")); }
        out: str = strSlice(self.text, self.pos, n);
        self.pos = self.pos + n;
        return out;
    }
    bad &self what:String -> void {
        failStr(format("{}: damaged metadata at byte {}: expected {}", self.origin, self.pos, what));
    }
}
