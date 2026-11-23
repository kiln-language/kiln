// File paths, as text. Nothing here touches the filesystem. These answer questions about the
// spelling of a path, and `file`/`dir` are what act on one.
//
//     dirOf("stdlib/sync.k")        // "stdlib"
//     baseName("stdlib/sync.k")     // "sync.k"
//     stemOf("stdlib/sync.k")       // "sync"
//     extOf("stdlib/sync.k")        // "k"
//
// Everything here answers with a view into the path it was given, so nothing allocates and this
// module needs neither `String` nor `Vec`. Building a path (joining, normalizing, splitting)
// is `pathbuf`, kept separate for that reason: `file` and `dir` include this one, so anything
// added here is compiled into every program that opens a file.
//
// Both separators are accepted everywhere, so a path written on Windows reads the same under
// Linux; `/` is what gets written back out.
#include <chars>

// The longest path the kernel takes (PATH_MAX), terminator included: the size of the buffer a
// path is copied into on its way to a syscall.
pub PATH_MAX: long = 4096;

// Every path-taking syscall wants a NUL-terminated C string, but a `str` is a {ptr, len} pair
// with no terminator. Copies the path and terminates it; returns the length written, or -1 when
// it cannot be passed on as written: too long for `dst`, or holding a NUL of its own, which the
// kernel would read as the end. A caller answers -1 with ENAMETOOLONG rather than open a
// different, shorter path than the one it was asked for.
pkg toCPath path:str inout dst:[u8] -> long {
    src: [u8] = path as [u8];
    if (src.len >= dst.len) { return -1; }
    for i in 0..src.len {
        if (src[i] == 0) { return -1; }
        dst[i] = src[i];
    }
    dst[src.len] = 0;
    return src.len;
}

pub isSep c:long -> bool { return c == '/' || c == '\\'; }

// An absolute path: one that starts at the root.
pub isAbsolute path:str -> bool { return isSep(charAt(path, 0)); }

// Where the last separator is, or -1. The one scan the splitting forms are built on.
pub lastSep path:str -> long {
    i: long = path.len;
    while (i > 0) {
        i -= 1;
        if (isSep(charAt(path, i))) { return i; }
    }
    return -1;
}

// The directory part: everything before the last separator, or "" if there is none. This is
// also how you climb one level: the parent of a directory is the directory part of it, which is
// why there is no second function for that.
pub dirOf path:str -> str {
    cut: long = lastSep(path);
    if (cut < 0) { return ""; }
    return strSlice(path, 0, cut);
}

// The last component, extension and all: `stdlib/sync.k` -> `sync.k`.
pub baseName path:str -> str {
    cut: long = lastSep(path);
    return strSlice(path, cut + 1, path.len - cut - 1);
}

// Where the extension's dot is in `base`, or -1. A leading dot is not an extension, so
// `.gitignore` has none.
local extDot base:str -> long {
    j: long = base.len;
    while (j > 1) {
        j -= 1;
        if (charAt(base, j) == '.') { return j; }
    }
    return -1;
}

// The last component with its extension removed: `stdlib/sync.k` -> `sync`.
pub stemOf path:str -> str {
    base: str = baseName(path);
    dot: long = extDot(base);
    if (dot < 0) { return base; }
    return strSlice(base, 0, dot);
}

// The extension without its dot, or "" if there is none.
pub extOf path:str -> str {
    base: str = baseName(path);
    dot: long = extDot(base);
    if (dot < 0) { return ""; }
    return strSlice(base, dot + 1, base.len - dot - 1);
}
