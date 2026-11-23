// `kilnc build [root] [-o exe] [--cache dir]`: build a program package by package.
//
// Reads the manifests from the root package down (the standard library is a package like the
// others, and every package depends on it), works out each package's KEY, and rebuilds only the
// packages whose `.klib` in the cache does not carry that key, in dependency order; then links the
// program if the root package defines `main`. A package's key is a 128-bit hash of everything its
// `.klib` is made from, by content:
//
//     the compiler (its own executable)    the package's name and manifest
//     every `.k` file in the package       the keys of its dependencies
//
// so changing a file changes its package's key, and through the dependency keys every package
// downstream of it, the way Rust's SVH propagates; and a package whose inputs did not change is
// not touched. Nothing here looks at a timestamp. A cached `.klib` with the right key is still
// checked whole before anything reads it (`usable`, `Klib.checkKlib`: every archive member there,
// the metadata's body against the hash its header gives), and one that is damaged or of another
// format is rebuilt from source with a note saying why, not reported as an error.
//
// The compiler is run once per stale package, as a separate process (this same executable, with
// `--klib`), then `nasm` and `ar`, and at the end `ld`, all found on PATH. A package's dependents
// need only its metadata, which the compiler writes before the object is assembled, so the next
// package compiles while the previous one's assembler and archiver run.
#include <Klib>
#include <support::compiler>
#include <pre::{PackageMap, Preprocessor}>
#include <stdlib::{dir, file, textfile, hash128, process, thread, io, map, option, result, sort, string, time, vec}>

local DEFAULT_CACHE: str = "build/klib";
// `Plan.byName`'s answer for a package whose dependencies are still being discovered: reaching it
// again is a cycle.
local DISCOVERING: long = -2;

// One package of the build: where it is, what it depends on, what it is made of.
local struct Pkg {
    name: str,
    root: str,
    firstDep: long, depCount: long,     // into `deps`: indices of other packages
    firstMember: long, memberCount: long,   // into `files`: the .k files in its root directory
    key: str,
    hasEntry: bool,
    // Where its dependents read its metadata: the archive when it was already current, the
    // compile's own output when it was rebuilt in this run (available before the archive is).
    meta: str,
    archive: str,          // its archive in the scratch directory, when it was built in this run
    checked: bool          // its cached archive was found whole in this run (`usable`)
}

local struct Plan {
    pkgs: Vec<Pkg>,
    deps: Vec<long>,
    files: Vec<str>,
    byName: HashMap<str, long>,
    order: Vec<long>,          // dependencies before dependents
    cache: str,
    compilerId: str,
    scratch: str,              // this run's own directory for intermediate files
    // The previous package's assembler and archiver, still running while the next compiles.
    pending: Vec<long>,        // pids
    pendingWhat: Vec<str>,
    built: long                // packages compiled in this run
}

pub runBuild args:[str] -> int {
    start: Instant = monotonic();
    root: str = ".";
    out: str = "";
    cache: str = DEFAULT_CACHE;
    i: long = 2;
    while (i < args.len) {
        x: str = args[i];
        if (x == "-o" || x == "--cache") {
            if (i + 1 >= args.len) { failStr(format("missing argument to `{}`", x)); }
            i = i + 1;
            if (x == "-o") { out = args[i]; } else { cache = args[i]; }
        } else if (x.len > 0 && charAt(x, 0) == '-') {
            failStr(format("unknown option `{}` to `kilnc build`\nhelp: `kilnc build` takes a package directory, `-o <exe>` and `--cache <dir>`", x));
        } else {
            root = x;
        }
        i = i + 1;
    }
    p: Plan = Plan { pkgs: vec![], deps: vec![], files: vec![], byName: map![], order: vec![],
                     cache: cache, compilerId: "", scratch: "", pending: vec![], pendingWhat: vec![], built: 0 };
    pm: PackageMap;
    // The root names a package's own directory: a manifest found further up is another package.
    if (!fileExists(joinKept(normalizeRoot(root), MANIFEST))) {
        failStr(format("no package to build in `{}`\nnote: a package's directory holds its `{}`", root, MANIFEST));
    }
    top: long = discover(&p, &pm, normalizeRoot(root));
    if (top < 0) { failStr(format("no package to build in `{}`\nnote: a package's directory holds its `{}`", root, MANIFEST)); }
    ensureDir(cache);
    p.scratch = makeScratch();

    // The compiler is an input to everything it builds.
    p.compilerId = compilerIdentity();

    for k in 0..p.order.len() {
        at: long = p.order.get(k);
        pk: Pkg = p.pkgs.get(at);
        // Current when the cached archive was built from exactly what is here now: the key it
        // carries is the one these files, this compiler and these dependencies make. Whether the
        // rest of it is whole is asked when something is about to read it (`usable`).
        klib: str = cachePath(&p, pk.name, ".klib");
        hdr: KlibHeader = readKlibHeader(klib);
        why: String;
        if (hdr.ok) {
            key: String = packageKey(&p, at, hdr.extras);
            same: bool = false;
            unsafe { same = hdr.key == key.view(); }
            if (same) {
                pk.key = keepString(key);
                pk.hasEntry = hdr.entry;
                pk.meta = klib;
                p.pkgs.set(at, pk);
                println("  fresh  {}", pk.name);
                continue;
            }
        } else if (hdr.present) {
            why = hdr.why;
        }
        if (!rebuild(&p, at, why)) { finishPending(&p); removeTree(p.scratch); return 1; }
    }
    if (!finishPending(&p)) { removeTree(p.scratch); return 1; }

    rootPkg: Pkg = p.pkgs.get(top);
    if (rootPkg.hasEntry) {
        exe: str = out;
        if (exe.len == 0) { exe = keepString(format("build/{}", rootPkg.name)); }
        if (!link(&p, top, exe)) { finishPending(&p); removeTree(p.scratch); return 1; }
    }
    removeTree(p.scratch);
    println("build: {} of {} packages rebuilt, {} ms", p.built, p.order.len(), elapsedMs(start));
    return 0;
}

// Package `at` compiled, saying first why when there was a cached archive that could not be used
// although its sources are these: one with another key is the ordinary rebuild, and says nothing.
// The rebuilt archive has the key the old one had, so its dependents are compiled as their keys
// say.
local rebuild inout p:Plan at:long why:String -> bool {
    pk: Pkg = p.pkgs.get(at);
    if (why.length() > 0) {
        flush();
        eprintln("note: rebuilding `{}`: its cached .klib {}", pk.name, why);
        flushErr();
    }
    one: Instant = monotonic();
    if (!compilePackage(p, at)) { return false; }
    pk = p.pkgs.get(at);
    p.built = p.built + 1;
    println("  built  {}  ({} ms)", pk.name, elapsedMs(one));
    flush();
    return true;
}

// Whether package `at`'s archive may be read now. One built in this run may. A cached one is
// checked whole the first time something is about to read it, a compile its metadata or the link
// its object (`Klib.checkKlib`: every member there, the format, the body against its hash), and
// rebuilt if it cannot be used, so a build with nothing to compile or link reads nothing past the
// headers.
local usable inout p:Plan at:long -> bool {
    pk: Pkg = p.pkgs.get(at);
    if (pk.archive.len > 0 || pk.checked) { return true; }
    c: KlibCheck = checkKlib(cachePath(p, pk.name, ".klib"));
    if (c.ok) {
        pk.checked = true;
        p.pkgs.set(at, pk);
        return true;
    }
    return rebuild(p, at, c.why);
}

// ─── the package graph ───────────────────────────────────────────────────────

local normalizeRoot r:str -> str {
    n: String = normalizePath(r);
    v: str = "";
    v = keepString(n);
    if (v.len == 0) { return "."; }
    return v;
}

// The package rooted at `dir`, its dependencies first, each added once. Every package but the
// standard library depends on it, as every file can include it without saying so.
local discover inout p:Plan inout pm:PackageMap dir:str -> long {
    idx: long = pm.loadAt(dir);
    if (idx < 0) { return -1; }
    info: PackageInfo = pm.at(idx);
    hit: Option<long> = p.byName.find(info.name);
    match hit {
        Some(at) {
            if (at == DISCOVERING) { failStr(format("package `{}` depends on itself", info.name)); }
            return at;
        }
        None { }
    }
    p.byName.put(info.name, DISCOVERING);
    mine: Vec<long>;
    for k in 0..pm.depCountAt(idx) {
        d: PackageDep = pm.depAt(idx, k);
        at: long = discover(p, pm, d.root);
        if (at < 0) { failStr(format("dependency `{}` has no `{}` at `{}`", d.name, MANIFEST, d.root)); }
        mine.push(at);
    }
    if (!(info.name == STDLIB_PKG)) {
        // Its own manifest, not the nearest one above where it should be: from a directory
        // without `stdlib/`, the walk up reaches the working directory's package.
        si: long = pm.loadAt(STDLIB_ROOT);
        if (si < 0 || !(pm.at(si).name == STDLIB_PKG)) {
            failStr(format("cannot find the standard library at `{}/{}`\nnote: paths are taken from the working directory\nhelp: run `kilnc build` from the directory that holds `{}/`, naming the package's directory (`kilnc build examples/ember`)",
                           STDLIB_ROOT, MANIFEST, STDLIB_ROOT));
        }
        mine.push(discover(p, pm, STDLIB_ROOT));
    }
    members: Vec<str> = membersOf(info.root);
    at: long = p.pkgs.len();
    p.pkgs.push(Pkg { name: info.name, root: info.root, firstDep: p.deps.len(), depCount: mine.len(),
                      firstMember: p.files.len(), memberCount: members.len(), key: "", hasEntry: false,
                      meta: "", archive: "", checked: false });
    p.deps.extend(mine);
    p.files.extend(members);
    p.byName.put(info.name, at);
    p.order.push(at);              // after its dependencies, which the recursion pushed first
    return at;
}

// A package's modules: the `.k` files in its root directory, sorted. A file further down that one
// of them includes is compiled with them (the scanner follows the include); its bytes are in the
// key through `sourcesOf` either way.
local membersOf dir:str -> Vec<str> {
    out: Vec<str>;
    d: Result<Dir, long> = openDir(dirOrDot(dir));
    match d {
        Err(_) { return out; }
        Ok(dd) {
            loop {
                e: Option<DirEntry> = dd.nextReal();
                if (e.isNone()) { break; }
                en: DirEntry = e.unwrap();
                name: str = "";
                unsafe { name = keep(en.view()); }
                if (strEndsWith(name, ".k") && !en.isDir()) { out.push(joinKept(dir, name)); }
            }
            dd.close();
        }
    }
    sort(&out);
    return out;
}

local joinKept dir:str leaf:str -> str {
    if (dir.len == 0 || dir == ".") { return leaf; }
    s: String = joinPath(dir, leaf);
    v: str = "";
    v = keepString(s);
    return v;
}


// ─── keys ────────────────────────────────────────────────────────────────────

// Package `at`'s key as its sources stand now (`Klib::klibKey`): the `.k` files of its root
// directory, plus whatever further files its last compile recorded reading (a module in a
// subdirectory that one of them includes). A member that starts including a new one has changed,
// so the key changes with it, and the next compile records the new file.
local packageKey inout p:Plan at:long extras:Vec<str> -> String {
    pk: Pkg = p.pkgs.get(at);
    srcs: Vec<str>;
    for k in 0..pk.memberCount { srcs.push(p.files.get(pk.firstMember + k)); }
    srcs.extend(extras);
    deps: Vec<KlibDep>;
    for k in 0..pk.depCount {
        d: Pkg = p.pkgs.get(p.deps.get(pk.firstDep + k));
        deps.push(KlibDep { name: d.name, key: d.key });
    }
    return klibKey(p.compilerId, pk.name, joinKept(pk.root, MANIFEST), srcs, deps);
}

// ─── one package ─────────────────────────────────────────────────────────────
//
// The intermediate files (the assembly, the object, the metadata, the archive while it is being
// put together, and the linked program) live in this run's own scratch directory under $TMPDIR,
// and only a finished `.klib` or executable is copied into the tree. The reason is the tools:
// `ar` and `ld` read and write with many small seeks, which costs nothing on a local disk and is
// forty times slower on a mounted one (WSL's /mnt/c, a network share), where a link that takes
// 40 ms took two seconds. A whole file copied in one pass is cheap on either.

local cachePath inout p:Plan name:str ext:str -> str {
    v: str = "";
    v = keepString(format("{}/{}{}", p.cache, name, ext));
    return v;
}
local scratchPath inout p:Plan name:str ext:str -> str {
    v: str = "";
    v = keepString(format("{}/{}{}", p.scratch, name, ext));
    return v;
}

// This run's scratch directory, made fresh.
local makeScratch -> str {
    base: str = "/tmp";
    t: Option<str> = envVar("TMPDIR");
    match t { Some(v) { if (v.len > 0) { base = v; } } None { } }
    dir: str = "";
    dir = keepString(format("{}/kiln-build-{}", base, processId()));
    if (dirExists(dir)) { removeTree(dir); }
    ensureDir(dir);
    return dir;
}

local removeTree dir:str -> void {
    args: Vec<str>;
    args.push("-rf");
    args.push(dir);
    gone: bool = runTool("rm", "rm", args);
}

// Compile package `at` against its dependencies' metadata, then assemble and archive it. The
// last two run in the background, so the next package's compile overlaps them.
local compilePackage inout p:Plan at:long -> bool {
    pk: Pkg = p.pkgs.get(at);
    // The metadata has to be called `kiln.meta` inside the archive, and `ar` names a member by
    // its file's own name: one directory per package.
    work: str = scratchPath(p, pk.name, "");
    ensureDir(work);
    asmPath: str = keepString(format("{}/{}.s", work, pk.name));
    objPath: str = keepString(format("{}/{}.o", work, pk.name));
    metaPath: str = keepString(format("{}/{}", work, KLIB_META));
    args: Vec<str>;
    args.push("--klib");
    for k in 0..pk.memberCount { args.push(p.files.get(pk.firstMember + k)); }
    args.push("--compiler-id"); args.push(p.compilerId);
    args.push("--meta"); args.push(metaPath);
    args.push("-o"); args.push(asmPath);
    // Every package below this one, not only the direct dependencies: an include reaches a
    // dependency's dependencies' modules too, and each comes from its own package's metadata.
    below: Vec<long>;
    seen: Vec<bool>;
    for k in 0..p.pkgs.len() { seen.push(false); }
    collectBelow(p, at, &seen, &below);
    for b in below {
        // Its metadata is read by the compile: checked first, and rebuilt if it cannot be used.
        if (!usable(p, b)) { return false; }
        d: Pkg = p.pkgs.get(b);
        args.push("--extern");
        args.push(keepString(format("{}={}", d.name, d.meta)));
    }
    flush();
    if (!runTool("/proc/self/exe", "kilnc", args)) { return false; }
    hdr: KlibHeader = readKlibHeader(metaPath);
    if (!hdr.ok) { eprintln("error: the compile of package `{}` wrote no usable metadata at `{}`", pk.name, metaPath); return false; }
    pk.hasEntry = hdr.entry;
    pk.meta = metaPath;
    unsafe { pk.key = keep(hdr.key.view()); }
    pk.archive = scratchPath(p, pk.name, ".klib");
    p.pkgs.set(at, pk);
    // The archive being replaced must not be mistaken for current while the job runs, or if it
    // fails.
    klib: str = cachePath(p, pk.name, ".klib");
    old: Result<long, long> = removeFile(klib);
    // nasm, then ar, as one background job that `sh -c` sequences without this process waiting;
    // the archive reaches the cache only once both have succeeded, under a temporary name that
    // is renamed into place, so a reader sees the old archive, none, or the whole new one.
    script: String = format("nasm -O1 -felf64 '{}' -o '{}' && ar rcsD '{}' '{}' '{}' && cp '{}' '{}.tmp' && mv -f '{}.tmp' '{}'",
                            asmPath, objPath, pk.archive, metaPath, objPath, pk.archive, klib, klib, klib);
    sargs: Vec<str>;
    sargs.push("-c");
    unsafe { sargs.push(keep(script.view())); }
    c: Result<Child, long> = spawnProcess("sh", sargs);
    match c {
        Ok(child) { p.pending.push(child.pid); p.pendingWhat.push(pk.name); }
        Err(e) { eprintln("error: cannot start the assembler for package `{}` (errno {})", pk.name, e); return false; }
    }
    return true;
}

local collectBelow inout p:Plan at:long inout seen:Vec<bool> inout out:Vec<long> -> void {
    pk: Pkg = p.pkgs.get(at);
    for k in 0..pk.depCount {
        d: long = p.deps.get(pk.firstDep + k);
        if (seen.get(d)) { continue; }
        seen.set(d, true);
        collectBelow(p, d, seen, out);
        out.push(d);
    }
}

// Wait for every background assembler; report each that failed.
local finishPending inout p:Plan -> bool {
    ok: bool = true;
    for k in 0..p.pending.len() {
        c: Child = Child { pid: p.pending.get(k) };
        st: Result<ExitStatus, long> = c.wait();
        match st {
            Ok(s) {
                if (!s.success()) {
                    eprintln("error: assembling and archiving package `{}` failed (the job {})", p.pendingWhat.get(k), s.describe());
                    ok = false;
                }
            }
            Err(e) { eprintln("error: cannot wait for the assembler of package `{}` (errno {})", p.pendingWhat.get(k), e); ok = false; }
        }
    }
    p.pending.clear();
    p.pendingWhat.clear();
    return ok;
}

// ─── the program ─────────────────────────────────────────────────────────────

// Link the root package's object and every package below it. The archives go in one group, so
// the order they are named in does not matter; `--gc-sections` drops every function no path
// from `_start` reaches, which is what keeps a library from costing a program its whole surface.
// The link is skipped when the executable is still the one this cache linked from exactly this
// root key. The stamp records the key (the compiler's identity and every package's sources,
// dependencies included), the path, and the size and modification time the executable had when
// it was written. Anything else that has written to the path since, such as another cache's
// build or a copy by hand, changes those, and the program is linked again.
local link inout p:Plan top:long exe:str -> bool {
    rootPkg: Pkg = p.pkgs.get(top);
    stamp: str = cachePath(p, rootPkg.name, ".link");
    want: String = format("{} {}\n", rootPkg.key, exe);
    have: Result<String, long> = readFileString(stamp);
    match have {
        Ok(s) {
            full: String = want.clone();
            now: String = exeStamp(exe);
            full.pushString(now);
            same: bool = false;
            unsafe { same = now.len() > 0 && s.view() == full.view(); }
            if (same) { println("  fresh  {} (linked)", exe); return true; }
        }
        Err(_) { }
    }
    // The link reads every archive: each is checked first, and rebuilt if it cannot be used,
    // its assembler done before `ld` runs.
    for k in 0..p.order.len() {
        if (!usable(p, p.order.get(k))) { return false; }
    }
    if (!finishPending(p)) { return false; }
    one: Instant = monotonic();
    // Every archive into the scratch directory: the ones built in this run are there already,
    // the rest are copied, one sequential read each.
    copies: Vec<str>;
    copies.push("-f");
    for k in 0..p.order.len() {
        pk: Pkg = p.pkgs.get(p.order.get(k));
        if (pk.archive.len == 0) { copies.push(cachePath(p, pk.name, ".klib")); }
    }
    copies.push(p.scratch);
    if (copies.len() > 2 && !runTool("cp", "cp", copies)) { return false; }
    out: str = scratchPath(p, "a", ".out");
    args: Vec<str>;
    args.push("--gc-sections");
    args.push("-e"); args.push("_start");
    args.push("-o"); args.push(out);
    args.push("--start-group");
    for k in 0..p.order.len() { args.push(scratchPath(p, p.pkgs.get(p.order.get(k)).name, ".klib")); }
    args.push("--end-group");
    gone: Result<long, long> = removeFile(stamp);
    if (!runTool("ld", "ld", args)) { return false; }
    place: Vec<str>;
    place.push("-f");
    place.push(out);
    place.push(exe);
    if (!runTool("cp", "cp", place)) { return false; }
    written: String = exeStamp(exe);
    if (written.len() > 0) {
        want.pushString(written);
        wrote: Result<long, long> = writeFileStr(stamp, "");
        unsafe { wrote = writeFileStr(stamp, want.view()); }
    }
    println("  linked {}  ({} ms)", exe, elapsedMs(one));
    return true;
}

// What the executable at `exe` is now, as the link stamp records it: its size and modification
// time, one line; empty when there is none.
local exeStamp exe:str -> String {
    out: String;
    m: Result<Metadata, long> = metadata(exe);
    match m {
        Ok(md) { out = format("{} {}\n", md.size, md.modifiedNs); }
        Err(_) { }
    }
    return out;
}

// ─── running tools ───────────────────────────────────────────────────────────

local runTool program:str shown:str args:Vec<str> -> bool {
    r: Result<ExitStatus, long> = runProcess(program, args);
    match r {
        Ok(s) {
            if (s.success()) { return true; }
            eprintln("error: `{}` {}", commandLine(shown, args), s.describe());
            return false;
        }
        Err(e) { eprintln("error: cannot run `{}` (errno {})", shown, e); return false; }
    }
    return false;
}

local commandLine shown:str args:Vec<str> -> String {
    s: String = stringOf(shown);
    for a in args { s.push(' '); s.pushStr(a); }
    return s;
}

local ensureDir path:str -> void {
    if (dirExists(path)) { return; }
    parent: str = dirOf(path);
    if (parent.len > 0 && !(parent == path)) { ensureDir(parent); }
    made: Result<long, long> = makeDir(path);
}

// The root package's directory normalizes to the empty path, which `openDir` cannot open.
local dirOrDot dir:str -> str {
    if (dir.len == 0) { return "."; }
    return dir;
}
