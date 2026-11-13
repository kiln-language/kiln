// Rewriting one file for the lexer: a `#file "path" 1 "package"` header in front, and every
// `#include <name>` replaced by a `#use "mod"` marker.
//
// One output line per input line, always, which is what keeps the lexer's running line number
// equal to the real one and error positions exact. Resolving the graph is the scanner's job.
#include <PackageMap>
#include <support::compiler>
#include <stdlib::{chars, path, pathbuf, string, fmt, map, file, io, option, sys, vec}>

// `STDLIB_PKG` and `STDLIB_ROOT` (the standard library's package and directory) are in
// `support::compiler`, where every phase can reach them.

// What separates a package from a module inside an include: `<pkg::mod>`.
local SEP: str = "::";

// Modules a `.klib` already holds, by the path they were read from: an include that resolves to
// one is taken without looking at the disk, because its text comes from the archive.
pub var gProvidedPaths: HashMap<str, bool> = map![];

// What a rewrite produced: the text, and the files every resolved include named, in source order.
pub struct Rewritten { text: String, includes: Vec<str> }

// Where an include was written: the file, the directory holding it, its package, and that
// package's index in the map. Derived once per file rather than once per include: asking the map
// again costs a path normalization, an intern and a hash every time, and a file's includes all
// have the same answer.
local struct Origin { path: str, dir: str, package: str, pkgIdx: long }

// Read `path` and rewrite it. `package` is the package the caller resolved this file into; it
// rides on the `#file` marker rather than a marker of its own, so the rewrite still emits one line
// per input line.
pub readModule inout pm:PackageMap path:str package:str -> Rewritten {
    at: Origin = Origin { path: path, dir: dirOf(path), package: package,
                          pkgIdx: pm.infoFor(path) };
    // Not `readSource`: a file that will not open is the preprocessor's diagnostic, worded the
    // way it words it, rather than the generic "could not open" the support layer would give.
    body: str = "";
    text: Option<str> = tryReadSource(path);
    match text {
        Some(t) { body = stripBom(t); }
        None    { failStr(format("Could not open file {}", path)); }
    }

    out: String;
    includes: Vec<str>;
    out.pushStr("#file \"");
    out.pushStr(path);
    out.pushStr("\" 1 \"");
    out.pushStr(package);
    out.pushStr("\"\n");

    lines: Vec<str> = splitLines(body);
    for line in lines {
        name: str = includeName(line);
        if (name.len == 0) {
            out.pushStr(line);
            out.push('\n');
        } else {
            // `<stdlib::{vec, map}>` is two includes, written on one line, so they are marked on
            // one: the line count in and out stays the same.
            names: Vec<str> = includeList(name, at);
            out.pushStr("#use");
            for one in names {
                includes.push(resolve(pm, one, at));
                // The import graph is keyed by module name, so record the module the include
                // names rather than how it was spelled: `<mathlib::vec>` and `<vec>` both name
                // module `vec`. The last component is always it, since resolution only ever looks
                // for `<name>.k`.
                out.pushStr(" \"");
                out.pushStr(lastComponent(one));
                out.push('"');
            }
            out.push('\n');
        }
    }
    return Rewritten { text: out, includes: includes };
}

// Editors on Windows often add a UTF-8 byte-order mark; the lexer would choke on the stray bytes.
local stripBom body:str -> str {
    if (charAt(body, 0) == 0xEF && charAt(body, 1) == 0xBB && charAt(body, 2) == 0xBF) {
        return strSlice(body, 3, body.len - 3);
    }
    return body;
}

// The part of `pkg::mod` after the separator, or the whole name if there is none. The last
// separator, so `a::b::c` names module `c`, what the file that resolution looked for is called.
local lastComponent name:str -> str {
    hit: Option<long> = strFindLast(name, SEP);
    cut: long = hit.unwrapOr(-1);
    if (cut < 0) { return name; }
    return strSlice(name, cut + 2, name.len - cut - 2);
}

// Every link is stated, never searched for. There are exactly two forms:
//
//   #include <mod>          a module of my own package, the file beside me
//   #include <pkg::mod>     a module of package `pkg`, which must be a declared dependency
//
// So you can read any include and know which package it comes from, without knowing the directory
// layout or the manifest. An unqualified name never leaves the package, which is why it cannot be
// ambiguous and why nothing needs a precedence rule: the old order (stdlib, then beside me, then
// each dependency in turn) meant the same include could mean different files depending on what
// happened to exist. Naming the package removes the tie instead of ranking it.
//
// Reports rather than returning "" on a miss: a mistyped include used to vanish and surface later
// as a baffling "Unknown type", pointing at the use instead of the include.
local resolve inout pm:PackageMap name:str at:Origin -> str {
    sep: long = findSep(name);

    if (sep >= 0) {
        pkgName: str = strSlice(name, 0, sep);
        mod:     str = strSlice(name, sep + 2, name.len - sep - 2);
        root:    str = "";
        if (pkgName == STDLIB_PKG) {
            root = STDLIB_ROOT;                       // implicit dependency of everything
        } else {
            root = depRoot(pm, at, pkgName);
        }
        target: str = keepJoin(root, mod);
        if (gProvidedPaths.has(target) || fileExists(target)) { return target; }
        failFrom(at.path, format("package '{}' has no module '{}' (looked for {})",
                                 pkgName, mod, target));
    }

    // `<mod>`: my own package, and nowhere else. A file beside me is usually in my package, but
    // not always: with no manifest above them, two files in one directory are two anonymous
    // packages, and reaching one from the other unqualified would be a cross-package link that
    // nothing declared. So the candidate's package is checked rather than assumed.
    if (at.dir.len > 0) {
        beside: str = keepJoin(at.dir, name);
        if (gProvidedPaths.has(beside) || fileExists(beside)) {
            if (pm.packageOf(beside) == at.package) { return beside; }
            failFrom(at.path, format("'{}' is beside this file but in a different package — neither directory declares a {}, so each file is its own package. Add one to put them in the same package.", name, MANIFEST));
        }
    }
    reportNoModule(pm, name, at);
    return "";
}

// What one `#include <...>` names. `<pkg::mod>` names one module; `<pkg::{a, b, c}>` names
// several of one package, each exactly as if it had its own line (`<{a, b}>` likewise for my own
// package). One level: a module name has no sub-path in this grammar (`a::b` past the package is
// one name, the file `a::b.k`), so a group cannot hold a group. Refused: an empty list, an empty
// item, a module named twice, and anything around the braces but a package and `::`.
local includeList name:str at:Origin -> Vec<str> {
    out: Vec<str>;
    open: long = strFind(name, "{").unwrapOr(-1);
    if (open < 0) {
        if (strFind(name, "}").unwrapOr(-1) >= 0) { failFrom(at.path, format("'<{}>': a '}' with no '{' to close", name)); }
        out.push(name);
        return out;
    }
    prefix: str = strSlice(name, 0, open);
    if (prefix.len > 0 && !(strEndsWith(prefix, SEP) && findSep(prefix) == prefix.len - 2 && prefix.len > 2)) {
        failFrom(at.path, format("'<{}>': a brace list follows a package and '::' (`<pkg::{{a, b}}>`), or stands alone for this package's own modules", name));
    }
    if (charAt(name, name.len - 1) != '}') {
        failFrom(at.path, format("'<{}>': the brace list must close the include, with '}' last", name));
    }
    inner: str = strSlice(name, open + 1, name.len - open - 2);
    if (strFind(inner, "{").unwrapOr(-1) >= 0 || strFind(inner, "}").unwrapOr(-1) >= 0) {
        failFrom(at.path, format("'<{}>': a brace list holds module names, not another list -- a module name has no sub-path to group", name));
    }
    if (strTrim(inner).len == 0) {
        failFrom(at.path, format("'<{}>': an empty list includes nothing -- name the modules, or drop the line", name));
    }
    items: Vec<str> = strSplit(inner, ',');
    seen: Vec<str>;
    for raw in items {
        item: str = strTrim(raw);
        if (item.len == 0) {
            failFrom(at.path, format("'<{}>': an empty name in the list (a stray ',')", name));
        }
        for earlier in seen {
            if (earlier == item) { failFrom(at.path, format("'<{}>': '{}' is listed twice", name, item)); }
        }
        seen.push(item);
        s: String;
        s.pushStr(prefix);
        s.pushStr(item);
        one: str = "";
        one = keepString(s);
        out.push(one);
    }
    return out;
}

// The root directory of `pkgName` as a declared dependency of the including file's package.
local depRoot inout pm:PackageMap at:Origin pkgName:str -> str {
    n: long = pm.depCountAt(at.pkgIdx);
    for i in 0..n {
        d: PackageDep = pm.depAt(at.pkgIdx, i);
        if (d.name == pkgName) { return d.root; }
    }
    failFrom(at.path, format("'{}' is not a declared dependency of this package — add `depend {} <path>` to its {}", pkgName, pkgName, MANIFEST));
    return "";
}

// The likely mistake is reaching for another package without saying so, and the fix depends on
// which: name a dependency already declared, or `stdlib`.
local reportNoModule inout pm:PackageMap name:str at:Origin -> void {
    s: String;
    s.pushStr("no module '");
    s.pushStr(name);
    s.pushStr("' in this package (looked for ");
    if (at.dir.len == 0) { s.pushStr("./"); } else { s.pushStr(at.dir); s.push('/'); }
    s.pushStr(name);
    s.pushStr(".k)");

    if (fileExists(keepJoin(STDLIB_ROOT, name))) {
        s.pushStr(" — it is a stdlib module: write <");
        s.pushStr(STDLIB_PKG);
        s.pushStr("::");
        s.pushStr(name);
        s.push('>');
    } else {
        for i in 0..pm.depCountAt(at.pkgIdx) {
            d: PackageDep = pm.depAt(at.pkgIdx, i);
            if (fileExists(keepJoin(d.root, name))) {
                s.pushStr(" — package '");
                s.pushStr(d.name);
                s.pushStr("' has it: write <");
                s.pushStr(d.name);
                s.pushStr("::");
                s.pushStr(name);
                s.push('>');
                break;
            }
        }
    }
    failFrom(at.path, s);
}

// `<dir>/<mod>.k`, kept by the interner so the result outlives this call.
pub keepJoin dir:str mod:str -> str {
    s: String;
    s.pushStr(dir);
    s.push('/');
    s.pushStr(mod);
    s.pushStr(".k");
    out: str = "";
    out = keepString(s);
    return out;
}

// Where `::` first appears in `name`, or -1, the first, so `<a::b::c>` names package `a` and
// leaves everything after it as the module, rather than silently reading a package out of the
// middle of the name.
local findSep name:str -> long {
    hit: Option<long> = strFind(name, SEP);
    return hit.unwrapOr(-1);
}

// `<file>: <what>`, every include error names the file that asked.
//
// Written straight to stderr rather than through `fail`, which puts `Error: ` in front. The
// reference compiler raises these four include diagnostics with no such banner. It is the one
// family of message in that compiler that has none, and this port's output is its output byte
// for byte. `PackageMap.reject` next door does go through `fail`, because the reference's
// manifest diagnostics do carry the banner. If the reference ever gains one here, this becomes
// `failStr(format("{}: {}", from, what))` and the difference disappears.
local failFrom from:str what:String -> void {
    eprintln("{}: {}", from, what);
    flushErr();
    sysExit(COMPILE_FAILED);
}

// The name in `#include <name>`, or "" if this line is not an include. Any surrounding whitespace
// is allowed, and the name is trimmed.
pub includeName line:str -> str {
    // A stray CR in front of the `#` does not hide the directive. Only here: a CR inside the
    // brackets stays part of the name, so `<x\r>` asks for a module nothing can resolve and
    // says so, rather than quietly meaning `x`.
    i: long = 0;
    while (isBlank(charAt(line, i)) || charAt(line, i) == '\r') { i = i + 1; }
    if (charAt(line, i) != '#') { return ""; }
    i = skipBlank(line, i + 1);
    if (!strStartsWith(strSlice(line, i, line.len - i), "include")) { return ""; }

    // From the start of the line, not from `i`: everything before the `#` is blank or CR and
    // everything between it and `i` is blank, so neither bracket can hide in there.
    lt: long = strFind(line, "<").unwrapOr(-1);
    gt: long = strFind(line, ">").unwrapOr(-1);
    if (lt < 0 || gt < 0 || gt <= lt) { return ""; }

    s: long = skipBlank(line, lt + 1);
    e: long = gt;
    while (e > s && isBlank(charAt(line, e - 1))) { e = e - 1; }
    if (e <= s) { return ""; }
    return strSlice(line, s, e - s);
}

local isBlank c:long -> bool { return c == ' ' || c == '\t'; }

local skipBlank line:str i:long -> long {
    k: long = i;
    while (isBlank(charAt(line, k))) { k = k + 1; }
    return k;
}
