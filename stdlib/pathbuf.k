// Building a path: the forms that allocate, split off from `path` (which only ever hands back a
// view into what it was given). Same split as `str` and `String`, and for the same reason —
// `file` and `dir` include `path`, so every program that opens a file would otherwise compile
// `String`, `Vec` and their dependencies whether or not it ever built a path.
//
//     joinNormalized("a/b", "../c/./d")   // "a/c/d"
//     withExt("src/main.k", "s")          // "src/main.s"
#include <{path, chars, string, vec}>

// `dir` and `leaf` with one separator between them. A leaf that is already absolute is the
// answer by itself, the way a shell resolves `cd /x` from anywhere.
pub joinPath dir:str leaf:str -> String {
    s: String;
    if (dir.len > 0 && !isAbsolute(leaf)) {
        s.pushStr(dir);
        if (!isSep(charAt(dir, dir.len - 1))) { s.push('/'); }
    }
    s.pushStr(leaf);
    return s;
}

// Split on either separator, dropping empty pieces. The pieces are views into `path`.
pub splitPath path:str -> Vec<str> {
    out: Vec<str>;
    start: long = 0;
    for i in 0..path.len + 1 {
        if (i == path.len || isSep(charAt(path, i))) {
            if (i > start) { out.push(strSlice(path, start, i - start)); }
            start = i + 1;
        }
    }
    return out;
}

// Collapse `.` and `..` so a path spells the same directory however it was reached — which is
// what lets a path be used as a map key without `a/../b` and `b` becoming two entries. A `..`
// with nothing to cancel is kept, since dropping it would climb out of a relative path — except
// at the root of an absolute path, which has no parent to climb to.
pub normalizePath path:str -> String {
    absolute: bool = isAbsolute(path);
    kept: Vec<str>;
    parts: Vec<str> = splitPath(path);
    for p in parts {
        if (p == "..") {
            if (kept.len() > 0 && kept.last() != "..") { kept.pop(); }
            else if (!absolute) { kept.push(p); }
        } else if (p != ".") {
            kept.push(p);
        }
    }
    out: String;
    // An absolute path stays absolute. `splitPath` drops the empty component a leading separator
    // makes, so the root has to be put back here — without it `/usr/lib` normalizes to `usr/lib`,
    // which names a different directory and silently resolves against the working one.
    if (absolute) { out.push('/'); }
    for i in 0..kept.len() {
        if (i > 0) { out.push('/'); }
        out.pushStr(kept.get(i));
    }
    return out;
}

// Join then collapse, which is how a relative path is resolved against the directory it was
// written in. One function because the two steps always happen together, and because doing them
// separately would make the caller take an `unsafe` view of the intermediate String.
pub joinNormalized dir:str leaf:str -> String {
    j: String = joinPath(dir, leaf);
    unsafe { return normalizePath(j.view()); }
}

// The same path with its extension replaced (`ext` without the dot), or added if it had none;
// an empty `ext` removes it.
pub withExt path:str ext:str -> String {
    out: String;
    out.pushStr(dirOf(path));
    if (lastSep(path) >= 0) { out.push('/'); }
    out.pushStr(stemOf(path));
    if (ext.len > 0) { out.push('.'); out.pushStr(ext); }
    return out;
}
