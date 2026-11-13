// The module import graph, and what each module can reach through it.
//
// A bare cross-module name (`Vec`, `Write`, `count`) resolves through the file that wrote it: its
// own module first, then what that file includes, transitively. The scanner walks the `#include`
// edges and publishes them here. Two modules may declare one name, so seeing both is ambiguous.
#include <compiler>
#include <stdlib::{map, sort, option, string, vec}>

// `NOT_FOUND` belongs to the registry, which sits above this package: a missing slot is spelled
// here instead.
local MISSING: long = -1;

// A contiguous stretch of a flat vector: how every variable-length part of this graph is stored,
// so the graph itself owns no nested containers.
pub struct Run { first: long, count: long }

pub struct ImportGraph {
    // The edges as scanned: `srcs[i]` includes `dsts[i]`. Grouped only once scanning is done,
    // because a depth-first walk finds a module's own edges interleaved with its children's.
    srcs: Vec<Sym>, dsts: Vec<Sym>,
    sealed: bool,

    outAt:   HashMap<str, long>,   // module -> its run of direct imports
    outs:    Vec<Run>,
    targets: Vec<Sym>,

    // Each closure is computed the first time it is asked for and kept: a name lookup asks per
    // call site, and the graph never changes after the scan.
    reachAt: HashMap<str, long>,
    reaches: Vec<Run>,
    reach:   Vec<Sym>
}

methods ImportGraph for Default {
    new -> ImportGraph {
        return ImportGraph { srcs: vec![], dsts: vec![], sealed: false,
                             outAt: map![], outs: vec![], targets: vec![],
                             reachAt: map![], reaches: vec![], reach: vec![] };
    }
}

methods ImportGraph {
    // One `#include` edge, by module name, which is what a bare name resolves through, and what
    // stays meaningful when two directories hold a module of the same name.
    note &self from:Sym to:Sym -> void {
        self.srcs.push(from);
        self.dsts.push(to);
    }

    // Group the edges by source. Two linear passes and a prefix sum rather than a scan per
    // module: the graph is walked far more often than it is built, but building it quadratically
    // is still the wrong shape.
    seal &self -> void {
        if (self.sealed) { return; }
        self.sealed = true;

        // Every distinct source, in first-seen order, with a run reserved for its edges.
        filled: Vec<long>;
        for src in self.srcs {
            key: str = nameOf(src);
            at: long = self.slotOf(key);
            if (at == MISSING) {
                at = self.outs.len();
                self.outAt.put(key, at);
                self.outs.push(Run { first: 0, count: 0 });
                filled.push(0);
            }
            r: Run = self.outs.get(at);
            self.outs.set(at, Run { first: 0, count: r.count + 1 });
        }

        cursor: long = 0;
        for run in &self.outs {
            run.first = cursor;
            cursor = cursor + run.count;
        }
        for i in 0..cursor { self.targets.push(NO_SYM); }

        for i in 0..self.srcs.len() {
            at: long = self.slotOf(nameOf(self.srcs.get(i)));
            r: Run = self.outs.get(at);
            self.targets.set(r.first + filled.get(at), self.dsts.get(i));
            filled.set(at, filled.get(at) + 1);
        }
    }

    slotOf &self key:str -> long {
        hit: Option<long> = self.outAt.find(key);
        match hit { Some(at) { return at; } None { } }
        return MISSING;
    }

    // Everything `here` can reach, transitively, not including itself. Breadth-first over the
    // grouped edges, memoized under `here`.
    visible &self here:str -> Run {
        self.seal();
        hit: Option<long> = self.reachAt.find(here);
        match hit { Some(at) { return self.reaches.get(at); } None { } }

        first: long = self.reach.len();
        seen: HashMap<str, long>;
        queue: Vec<Sym>;
        // Collected here and sorted before it joins `reach`, so `reaches` below can binary-search
        // it. Membership used to be a walk, on the reasoning that a run is "a handful of
        // entries": true of this compiler's 52 modules and not of a program with a thousand,
        // where a name lookup per call site over a list per module is the whole cost of a build.
        found: Vec<Sym>;
        at: long = self.slotOf(here);
        if (at != MISSING) {
            r: Run = self.outs.get(at);
            for k in 0..r.count { queue.push(self.targets.get(r.first + k)); }
        }
        head: long = 0;
        while (head < queue.len()) {
            m: Sym = queue.get(head);
            head = head + 1;
            key: str = nameOf(m);
            if (seen.has(key)) { continue; }
            seen.put(key, 1);
            found.push(m);
            mat: long = self.slotOf(key);
            if (mat == MISSING) { continue; }
            r: Run = self.outs.get(mat);
            for k in 0..r.count { queue.push(self.targets.get(r.first + k)); }
        }

        sort(&found);
        self.reach.extend(found);
        out: Run = Run { first: first, count: self.reach.len() - first };
        self.reaches.push(out);
        self.reachAt.put(keep(here), self.reaches.len() - 1);
        return out;
    }

    visibleAt &self r:Run k:long -> Sym { return self.reach.get(r.first + k); }

    // Can a file in module `here` name something declared in `m`? Its own module always, and
    // anything it includes. A binary search over the sorted closure: this is asked once per
    // candidate declaration of a bare name, where the old arrangement asked the opposite question
    // once per visible module, and the difference between those two is what made a program's
    // build quadratic in its module count.
    reaches &self here:str m:Sym -> bool {
        if (here == nameOf(m)) { return true; }
        r: Run = self.visible(here);
        lo: long = 0;
        hi: long = r.count;
        while (lo < hi) {
            mid: long = lo + (hi - lo) / 2;
            v: Sym = self.reach.get(r.first + mid);
            if (v == m) { return true; }
            if (v < m) { lo = mid + 1; } else { hi = mid; }
        }
        return false;
    }

    canReach &self here:str mod:str -> bool { return self.reaches(here, intern(mod)); }

    // Whether the scan found any edges at all. A single-file program has none, and every name in
    // it is its own module's: asking the graph would refuse them all.
    isEmpty &self -> bool { return self.srcs.len() == 0; }
}

// One graph for the whole compile, for the same reason there is one interner: every phase that
// resolves a name asks it, and threading it through every signature would buy nothing.
pub var gImports: ImportGraph;
