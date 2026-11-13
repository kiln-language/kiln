// A Module is one compilation unit: a single `.k` source file.
//
// That is the unit the `#include` graph hands us and the one the namespacing system already uses.
// A module is not a package: a package is a declared collection of modules, and is what `pkg`
// visibility answers to. Modules are keyed by path, since two trees may both hold a `sync`.
#include <support::compiler>

pub struct Module {
    name:    str,     // the file's basename, e.g. "io"
    path:    str,     // the file itself, e.g. "stdlib/io.k"
    package: str,     // the package it was declared into, e.g. "stdlib"
    index:   long,    // position in the topological order

    // This module's source, already rewritten for the lexer: a `#file` header followed by the
    // file's own lines with each `#include <m>` turned into a `#use "m"` marker. Nothing is
    // spliced in, so the line count (and every error location) is exactly the file's own.
    source:  str,

    firstImport: long, importCount: long,   // direct `#include` edges, in source order
    firstDep:    long, depCount:    long    // transitive closure, topologically ordered
}
