// Which package a source file belongs to, and what it may depend on.
//
// A `package.kiln` manifest at a directory root declares a package, and its members are that
// subtree, stopping at any nested manifest. A file with no manifest above it is its own anonymous
// package. A manifest may `depend <name> <path>`; dependencies do not chain, and a cycle is
// refused here, while the manifest chain that produced it can still be named.
#include <support::compiler>
#include <stdlib::{chars, path, pathbuf, string, fmt, map, option, panic, vec}>

pub MANIFEST: str = "package.kiln";

pub NO_PACKAGE: long = -1;

// One dependency edge: the name a manifest gave it, and the directory it lives in.
pub struct PackageDep { name: str, root: str }

// One `depend` line as written, before its path is resolved. Reading a manifest and resolving
// what it depends on are separate steps, because the package has to be registered before the
// recursion that reads its dependencies' manifests: otherwise a cycle runs away instead of
// being named.
local struct RawDep { name: str, path: str }

// A declared package. Its dependencies are a run in the map's flat `deps` vector rather than a
// vector of their own, which is what keeps this Copy. The run is contiguous because a package's
// edges are appended in one block, after the recursion that resolved them has finished appending
// everyone else's.
pub struct PackageInfo { name: str, root: str, firstDep: long, depCount: long }

pub struct PackageMap {
    infos:     Vec<PackageInfo>,
    deps:      Vec<PackageDep>,
    byDir:     HashMap<str, long>,   // directory -> index into infos, or NO_PACKAGE
    resolving: Vec<str>              // manifest roots whose dependencies are being read
}

methods PackageMap for Default {
    new -> PackageMap {
        return PackageMap { infos: vec![], deps: vec![], byDir: map![], resolving: vec![] };
    }
}

methods PackageMap {
    // ─── what the rest of the compiler asks ──────────────────────────────────

    // The package `path` belongs to. With no manifest above it, its own path, so nothing else
    // can compare equal, and `pkg` means exactly file-private for it.
    packageOf &self path:str -> str {
        idx: long = self.infoFor(path);
        if (idx < 0) { return path; }
        return self.infos.get(idx).name;
    }

    // The manifest governing `path`, as an index into `infos`, or NO_PACKAGE.
    infoFor &self path:str -> long { return self.nearest(dirOf(path)); }

    // The directory the governing manifest sits at (the root of `path`'s package) or "" if no
    // manifest governs it. What a report over a package's own files needs: `packageOf` names the
    // package, this says where to look for the rest of it.
    rootOf &self path:str -> str {
        idx: long = self.infoFor(path);
        if (idx < 0) { return ""; }
        return self.infos.get(idx).root;
    }

    // The direct dependencies of package `idx`. There is no way to hand back a borrowed slice, so
    // the run is read through these two rather than returned whole, and both take the index, not
    // the path, so a caller resolves its package once instead of paying a path normalization and
    // a hash for every edge it walks. NO_PACKAGE has none, which is right: you cannot depend on
    // anything without a manifest to say so in.
    depCountAt &self idx:long -> long {
        if (idx < 0) { return 0; }
        return self.infos.get(idx).depCount;
    }

    // Dependency `k` of package `idx`, in declaration order.
    depAt &self idx:long k:long -> PackageDep {
        info: PackageInfo = self.infos.get(idx);
        if (k < 0 || k >= info.depCount) { panicIndex("PackageMap.depAt", k, info.depCount); }
        return self.deps.get(info.firstDep + k);
    }

    // Every package a manifest has been read for. The package graph is built from these rather
    // than from include edges, so it is complete before any source is lexed.
    count &self -> long { return self.infos.len(); }
    at    &self i:long -> PackageInfo { return self.infos.get(i); }

    // Read the manifest at `root`, and its dependencies' transitively. Pulls in a package nothing
    // has opened a file from yet.
    loadAt &self root:str -> long { return self.nearest(root); }

    // ─── walking up for a manifest ───────────────────────────────────────────

    // The package declared at or above `dir`, or NO_PACKAGE. Memoized per directory, so the walk
    // happens once per branch.
    //
    // The directory is normalized first, because the memo and the cycle stack are both keyed by
    // the string. A path arrives here two ways (from a source file the driver was handed, and
    // from a manifest's relative dependency) and if those spellings key separately the same
    // package is read twice under two entries, and a cycle is only noticed on the second lap with
    // the wrong package named as its start.
    nearest &self rawDir:str -> long {
        dir: str = self.held(normalizePath(rawDir));
        hit: Option<long> = self.byDir.find(dir);
        match hit { Some(at) { return at; } None { } }
        self.byDir.put(dir, NO_PACKAGE);        // guard: a cycle must not recurse forever

        manifest: str = self.held(joinPath(dir, MANIFEST));
        text: Option<str> = tryReadSource(manifest);
        body: str = "";
        match text {
            Some(t) { body = t; }
            None {
                up: long = NO_PACKAGE;
                if (dir.len > 0) { up = self.nearest(dirOf(dir)); }   // keep climbing
                self.byDir.put(dir, up);
                return up;
            }
        }

        // Register before resolving dependencies, so the recursion terminates on a cycle rather
        // than running away; `resolving` is what turns that termination into a diagnosis.
        raw: Vec<RawDep>;
        name: str = self.readManifest(body, manifest, &raw);
        self.infos.push(PackageInfo { name: name, root: dir, firstDep: 0, depCount: 0 });
        idx: long = self.infos.len() - 1;
        self.byDir.put(dir, idx);

        self.resolving.push(dir);
        mine: Vec<PackageDep> = self.resolveDeps(manifest, dir, raw);
        self.resolving.pop();

        info: PackageInfo = self.infos.get(idx);
        info.firstDep = self.deps.len();
        info.depCount = mine.len();
        self.infos.set(idx, info);
        self.deps.extend(mine);
        return idx;
    }

    // Hand a built String to the interner and keep only the view. Every string this map stores
    // goes through here, which is what lets the map hold views instead of owning buffers.
    held &self s:String -> str {
        out: str = "";
        out = keepString(s);
        return out;
    }

    // ─── the manifest ────────────────────────────────────────────────────────
    // A manifest is not source and is not lexed: it is read here directly. Two directives, both
    // one line:  `package <name>;`  and  `depend <name> <path>`.

    // One pass, the directives judged in the order they were written, so the first bad line is
    // the one reported. Returns the declared name and fills `raw` with the `depend` lines still
    // as written: resolving one reads another manifest, and that cannot happen until this
    // package is registered. A word is a view into `body`, which the source cache holds for the
    // whole compile, so only the names are interned: those are what later gets compared.
    readManifest &self body:str manifest:str inout raw:Vec<RawDep> -> str {
        found: str = "";
        lines: Vec<str> = splitLines(body);
        for line in lines {
            w: Vec<str> = words(line);
            if (w.len() > 0) {
                head: str = w.get(0);
                if (head == "package") {
                    if (found.len > 0) { self.reject(manifest, stringOf("declares more than one package")); }
                    if (w.len() < 2) { self.reject(manifest, stringOf("package has no name")); }
                    found = keep(w.get(1));
                } else if (head == "depend") {
                    if (w.len() < 3) {
                        self.reject(manifest, stringOf("`depend` needs a name and a path (depend mathlib ../mathlib)"));
                    }
                    raw.push(RawDep { name: keep(w.get(1)), path: w.get(2) });
                } else {
                    self.reject(manifest,
                                format("unknown directive '{}' (expected `package` or `depend`)",
                                       head));
                }
            }
        }
        // Not `reject`: a manifest that declares nothing is faulted as a whole, not at a line in it.
        if (found.len == 0) { failStr(format("{} declares no package", manifest)); }
        return found;
    }

    // Resolve every `depend` line, in declaration order.
    resolveDeps &self manifest:str dir:str raw:Vec<RawDep> -> Vec<PackageDep> {
        out: Vec<PackageDep>;
        for d in raw { out.push(self.resolveDep(manifest, dir, d)); }
        return out;
    }

    // One dependency: check it closes no cycle, read its manifest, and check that both ends agree
    // on the name.
    resolveDep &self manifest:str dir:str d:RawDep -> PackageDep {
        dname: str = d.name;
        depRoot: str = self.held(joinNormalized(dir, d.path));

        for i in 0..self.resolving.len() {
            if (self.resolving.get(i) == depRoot) { self.reportCycle(i, depRoot); }
        }

        at: long = self.nearest(depRoot);
        if (at < 0) {
            self.reject(manifest, format("dependency '{}' has no {} at {}",
                                         dname, MANIFEST, depRoot));
        }
        declared: str = self.infos.get(at).name;
        if (!(declared == dname)) {
            theirs: String = joinPath(depRoot, MANIFEST);
            self.reject(manifest,
                        format("dependency is named '{}' but {} declares package '{}'",
                               dname, theirs, declared));
        }
        return PackageDep { name: dname, root: depRoot };
    }

    // Name the packages in the chain and list their roots after it: the names are what the
    // manifests say and what the reader has to change, and the roots are how to find them.
    // `depRoot` closes the loop back to entry `from`; `from` being the last entry is a package
    // that depends on itself directly.
    reportCycle &self from:long depRoot:str -> void {
        s: String;
        roots: String;
        s.pushStr("package dependency cycle: ");
        for j in from..self.resolving.len() {
            root: str = self.resolving.get(j);
            s.pushStr(self.nameAt(root));
            s.pushStr(" -> ");
            if (roots.length() > 0) { roots.pushStr(", "); }
            roots.pushStr(root);
        }
        s.pushStr(self.nameAt(depRoot));
        s.pushStr(" — a package may not depend on itself, directly or through others (roots: ");
        s.pushString(roots);
        s.push(')');
        failStr(s);
    }

    // The package declared at `dir`, which is on the resolving stack and so already registered.
    // Only ever called to build a diagnostic.
    nameAt &self dir:str -> str {
        hit: Option<long> = self.byDir.find(dir);
        match hit {
            Some(i) { if (i >= 0) { return self.infos.get(i).name; } }
            None { }
        }
        return dir;
    }

    // `<manifest>: <what>`, through `fail`, a manifest diagnostic carries the `Error: ` banner,
    // unlike an include diagnostic next door. That split is the reference's, not a slip here.
    reject &self manifest:str what:String -> void {
        failStr(format("{}: {}", manifest, what));
    }
}

// ─── manifest text ───────────────────────────────────────────────────────────

// A line split into words, with a trailing `;` and any `//` or `#` comment dropped. An empty
// result means the line said nothing.
pub words line:str -> Vec<str> {
    out: Vec<str>;
    start: long = -1;
    i: long = 0;
    going: bool = true;
    while (going && i <= line.len) {
        c: long = charAt(line, i);
        // One past the end closes the last word, and so does the start of a comment.
        stop: bool = i == line.len || c == '#' || (c == '/' && charAt(line, i + 1) == '/');
        if (stop || c == ' ' || c == '\t' || c == '\r' || c == ';') {
            if (start >= 0) { out.push(strSlice(line, start, i - start)); start = -1; }
            if (stop) { going = false; }
        } else if (start < 0) {
            start = i;
        }
        i = i + 1;
    }
    return out;
}
