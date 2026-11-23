// Which code this compile owns, and which arrived already compiled.
//
// A package build (`--klib`) reads its dependencies out of their `.klib`s: their source is parsed
// here like any other, so their declarations, templates and macros are all in the tree, but their
// non-generic bodies were checked and compiled when their own package was, and are not again.
// Such a function is EXTERNAL: every phase after parsing leaves its body alone, takes what it
// would have inferred from the facts table its `.klib` carries, and the emitter references its
// symbol. The one exception is a body the compile-time evaluator has to run (a macro, or code a
// global's initializer reaches): that one is checked here on demand, and run, and still not
// emitted.
//
// Generic templates are never external: a template has no symbol until it is stamped. An instance
// is stamped here, and each of its functions is then one of three things: external, when a
// dependency compiled and exported it (its `.klib`'s INSTFNS, `markExtern`); lazy, when a
// dependency stamped the instance but compiled no such function, so this package compiles it only
// if its code reaches it; or this package's own, compiled and exported in turn.
#include <{ast, registry}>
#include <support::compiler>
#include <stdlib::{map, option, vec}>

// Building one package into a `.klib`, rather than a whole program into one object.
pub var gKlibMode: bool = false;
// The package being built, in klib mode.
pub var gThisPkg: Sym = NO_SYM;
// The packages whose code came from a `.klib`, by name.
pub var gUpstreamPkgs: HashMap<str, bool> = map![];

// Per function, by its index in the tree's `fns`: an upstream source function this compile does
// not compile. Sized once, after parsing; anything appended later (a stamped instance, drop glue,
// a derived method) is this compile's own by construction.
pub var gExternFn: Vec<bool> = vec![];
// Per function, the same index: an external body that has been checked here, on demand, because
// the evaluator has to run it. The evaluator refuses an external body that is not.
pub var gExternReady: Vec<bool> = vec![];
// How many functions the parser made (and a `.klib` brought): everything after them in `fns` was
// made by a later phase, and is this compile's own.
pub var gParsedCount: long = 0;

pub isUpstreamPkg pkg:Sym -> bool {
    if (pkg == NO_SYM || gUpstreamPkgs.isEmpty()) { return false; }
    return gUpstreamPkgs.has(nameOf(pkg));
}

pub isExternFn at:long -> bool {
    if (at < 0 || at >= gExternFn.len()) { return false; }
    return gExternFn.get(at);
}

// An external or lazy body checked here: the evaluator may run it, and a lazy one is compiled.
pub isExternReady at:long -> bool {
    if (at < 0 || at >= gExternReady.len()) { return false; }
    return gExternReady.get(at);
}
pub markExternReady at:long -> void {
    while (gExternReady.len() <= at) { gExternReady.push(false); }
    gExternReady.set(at, true);
}

// The generic struct instances some dependency already stamped, which means it also cloned and
// checked every one of their methods. They are stamped here again, since an instance has no
// symbol outside the object that stamped it, but their methods are LAZY: each one is checked and
// compiled only if this package's code reaches it. Anything wrong with one was already reported
// where the instance was first made.
pub var gKnownInstances: HashMap<str, bool> = map![];
pub var gLazyFn: Vec<bool> = vec![];

pub isLazyFn at:long -> bool {
    if (at < 0 || at >= gLazyFn.len()) { return false; }
    return gLazyFn.get(at);
}
// A method another package compiled and this one links to (`markExtern`) is not lazy: it is
// never compiled here at all.
pub markLazy first:long end:long -> void {
    while (gLazyFn.len() < end) { gLazyFn.push(false); }
    for k in first..end {
        if (!isExternFn(k)) { gLazyFn.set(k, true); }
    }
}

// ─── instances another package compiled ─────────────────────────────────────
//
// A generic instance's function (a method of `Vec<long>`, `vecOf<long>`) that a dependency
// checked, compiled and exported is EXTERNAL here, exactly as a dependency's source function is:
// monomorphization decides it (`Mono.reuseOf`) and marks it, its facts come from that `.klib`,
// and every reference to it is written as the owner's symbol, which `gLinkAlias` gives by name.
pub markExtern at:long -> void {
    while (gExternFn.len() <= at) { gExternFn.push(false); }
    gExternFn.set(at, true);
}

// A function's link label when it is not the one its name spells: an instance function another
// package compiled, by its name, to that package's alias for it (`fnLabel` asks).
pub var gLinkAlias: HashMap<str, str> = map![];

// What this compile's own instance functions were compiled against (`Mono.fingerprint`), by name:
// the owner's half of the check a dependent makes before it links to one. Filled for every clone
// in a package build.
pub var gInstanceFp: HashMap<str, long> = map![];

// How many implementations the registry held when parsing ended. Those, and only those, are the
// ones the source declares; a derived one, or one an instance restates, comes after them. The
// fingerprint is computed from this set, in the owner and in the dependent alike, so both sides
// see the same implementations.
pub var gDeclaredImpls: long = 0;

// A body this compile has not checked and will not compile: a dependency's, or a lazy method
// nothing reached. Every phase after checking leaves it alone.
pub isUnchecked at:long -> bool {
    return (isExternFn(at) || isLazyFn(at)) && !isExternReady(at);
}

// A global another package owns: its storage, and its initializer, are that package's.
pub isExternGlobal n:Sym -> bool {
    if (gUpstreamPkgs.isEmpty()) { return false; }
    gi: long = gReg.findGlobalSym(n);
    if (gi < 0) { return false; }
    return isUpstreamPkg(gReg.globalDef(gi).pkg);
}

// Is a parsed function this package's own source: not a template, written in this package.
pub isOwnSourceFn inout a:Ast at:long -> bool {
    if (!gKlibMode || at < 0 || at >= gParsedCount) { return false; }
    f: FnNode = a.fns.get(at);
    return !f.isTemplate && f.pkg == gThisPkg;
}

// Once, right after parsing: which functions are external.
pub noteParsedFunctions inout a:Ast -> void {
    gExternFn.clear();
    gExternReady.clear();
    gParsedCount = a.fns.len();
    gDeclaredImpls = gReg.implCount();
    for i in 0..a.fns.len() {
        f: FnNode = a.fns.get(i);
        gExternFn.push(!f.isTemplate && hasBody(f) && isUpstreamPkg(f.pkg));
        gExternReady.push(false);
    }
}
