// The scan phase: turn a root `.k` file into a module dag.
//
// It walks the `#include` graph depth-first, calling the preprocessor once per file, and produces
// one Module per source file in DFS post-order, dependencies before dependents, which is the order
// declaration merging and `.data` emission need. Include cycles are caught here, path in hand.
#include <{Module, Klib}>
#include <pre::{PackageMap, Preprocessor}>
#include <support::{compiler, imports}>
#include <stdlib::{path, pathbuf, file, map, option, sort, string, vec}>

pub struct Scanner {
    modules:   Vec<Module>,       // in topological (DFS post) order
    imports:   Vec<long>,         // each module's direct edges, as a run
    deps:      Vec<long>,         // each module's transitive closure, as a run
    packages:  PackageMap,
    byPath:    HashMap<str, long>,// resolved path -> module index (dedupe)
    onStack:   Vec<str>           // paths on the current DFS path, for cycle reporting
}

methods Scanner for Default {
    new -> Scanner {
        p: PackageMap;
        return Scanner { modules: vec![], imports: vec![], deps: vec![],
                         packages: p, byPath: map![], onStack: vec![] };
    }
}

methods Scanner {
    // Scan from `rootPath`. Reports and exits on a missing file or an include cycle.
    scan &self rootPath:str -> void {
        roots: Vec<str>;
        roots.push(rootPath);
        self.scanAll(roots);
    }

    // Several roots, in the order given: a package build compiles every module of its package,
    // and each is a root, since nothing in the package has to include all the rest.
    scanAll &self roots:Vec<str> -> void {
        // `stdlib::core` declares the traits the compiler wires into the language (`Drop`,
        // `Clone`, `Default`, `Eq`, `Add`...), so it is in every program, first, whether or not
        // anything includes it. Otherwise a `methods X for Drop` in a file that includes nothing
        // would name a trait nobody declared, and the drop would never run. Since it is visited
        // as no module's include, it adds no import edge; its traits are flat names any module
        // resolves.
        corePath: str = keepJoin(STDLIB_ROOT, "core");
        if (gProvidedPaths.has(corePath) || fileExists(corePath)) { self.visit(corePath); }
        for root in roots { self.visit(keep(root)); }
        // A macro is written against `stdlib::ast`'s `Node`, and its declaration is read once
        // the whole program has been. So a program that declares one has `ast` in it, whether
        // or not any module could include it (`vec` cannot: `ast` is built on `Vec`).
        if (self.declaresMacro()) {
            astPath: str = keepJoin(STDLIB_ROOT, "ast");
            if (gProvidedPaths.has(astPath) || fileExists(astPath)) { self.visit(astPath); }
        }
        self.computeTransitiveDeps();
        // The import graph is finished the moment the walk is: every later phase that resolves a
        // bare cross-module name reads it, and none of them can see the scanner.
        gImports.seal();
    }

    // Does any module declare a `macro`? One a `.klib` brought says so in its directory entry.
    declaresMacro &self -> bool {
        for m in self.modules {
            kk: long = klibModule(m.path);
            if (kk >= 0) { if (gKlibModules.get(kk).hasMacro) { return true; } continue; }
            if (moduleDeclaresMacro(m.source)) { return true; }
        }
        return false;
    }

    count &self -> long { return self.modules.len(); }
    at    &self i:long -> Module { return self.modules.get(i); }

    importAt &self m:Module k:long -> long { return self.imports.get(m.firstImport + k); }
    depAt    &self m:Module k:long -> long { return self.deps.get(m.firstDep + k); }

    // Depth-first: read the file, visit each include, then append this module. Post-order
    // placement is what puts dependencies before dependents.
    visit &self path:str -> long {
        done: Option<long> = self.byPath.find(path);
        match done { Some(at) { return at; } None { } }
        if (self.onStackHas(path)) { self.reportCycle(path); }

        self.onStack.push(path);
        pkg: str = "";
        text: str = "";
        includes: Vec<str>;
        // A module a dependency's `.klib` carries is taken from there, already rewritten, with
        // the includes it resolved when that package was built: no file is opened for it.
        kk: long = klibModule(path);
        if (kk >= 0) {
            km: KlibModule = gKlibModules.get(kk);
            pkg = km.pkg;
            // No text: the module arrives already parsed (`KlibTree.loadModuleSection`).
            for k in 0..km.includeCount { includes.push(gKlibIncludes.get(km.firstInclude + k)); }
        } else {
            pkg = self.packages.packageOf(path);
            m: Rewritten = readModule(&self.packages, path, pkg);
            text = keepString(m.text);
            includes.extend(m.includes);
        }

        // The preprocessor hands back resolved paths, because the same module name can mean
        // different files in different directories. The import graph stays keyed by module name,
        // because that is what the parser resolves bare cross-module names through. The edge is
        // recorded for every importer, not just the first: each one needs its own edges.
        name: str = stemOf(path);
        mine: Vec<long> = self.visitIncludes(includes, name);
        self.onStack.pop();

        idx: long = self.modules.len();
        self.modules.push(Module { name: name, path: path, package: pkg, index: idx,
                                   source: text,
                                   firstImport: self.imports.len(), importCount: mine.len(),
                                   firstDep: 0, depCount: 0 });
        self.imports.extend(mine);
        self.byPath.put(path, idx);
        return idx;
    }

    // Visit each include and collect the module indices. Held locally and appended by the caller
    // in one block, so this module's run stays contiguous while the recursion appends others'.
    visitIncludes &self includes:Vec<str> name:str -> Vec<long> {
        out: Vec<long>;
        for p in includes {
            gImports.note(intern(name), intern(stemOf(p)));
            out.push(self.visit(p));
        }
        return out;
    }

    onStackHas &self path:str -> bool {
        for p in self.onStack {
            if (p == path) { return true; }
        }
        return false;
    }

    // Each module's seed: every module it transitively includes, in topological order. Post-order
    // guarantees a module's index exceeds all of its dependencies', so unioning its children's
    // already-complete closures is enough, and a sorted list of indices is already topologically
    // ordered.
    computeTransitiveDeps &self -> void {
        for m in &self.modules {
            gathered: Vec<long>;
            for k in 0..m.importCount {
                imp: long = self.imports.get(m.firstImport + k);
                gathered.push(imp);
                child: Module = self.modules.get(imp);
                for j in 0..child.depCount { gathered.push(self.deps.get(child.firstDep + j)); }
            }
            sort(&gathered);

            m.firstDep = self.deps.len();
            m.depCount = 0;
            prev: long = -1;
            for v in gathered {
                if (v != prev && v != m.index) {    // deduped, and a module never seeds itself
                    self.deps.push(v);
                    m.depCount = m.depCount + 1;
                }
                prev = v;
            }
        }
    }

    reportCycle &self repeat:str -> void {
        s: String;
        s.pushStr("include cycle: ");
        started: bool = false;
        for p in self.onStack {
            if (p == repeat) { started = true; }
            if (started) { s.pushStr(p); s.pushStr(" -> "); }
        }
        s.pushStr(repeat);
        failStr(s);
    }
}

// Does a module's text declare a `macro`? A line's first word, after its visibility.
pub moduleDeclaresMacro text:str -> bool {
    lines: Vec<str> = splitLines(text);
    for line in lines {
        t: str = strTrim(line);
        if (strStartsWith(t, "pub ")) { t = strTrim(strSlice(t, 4, t.len - 4)); }
        else if (strStartsWith(t, "pkg ")) { t = strTrim(strSlice(t, 4, t.len - 4)); }
        else if (strStartsWith(t, "local ")) { t = strTrim(strSlice(t, 6, t.len - 6)); }
        if (strStartsWith(t, "macro ")) { return true; }
    }
    return false;
}
