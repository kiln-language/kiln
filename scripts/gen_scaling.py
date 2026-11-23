#!/usr/bin/env python3
"""Generate synthetic programs that grow along ONE axis at a time.

Compile time growing with the size of a program is expected; growing FASTER than the program is a
bug with a shape. Four families, because the candidates in this compiler sit in different places
and only a per-axis curve tells them apart:

  functions   one module, N functions in a chain from `main`. Grows the page, the IR, and the
              number of frames the allocator sees.

  modules     N modules, each including the one before it: a DEEP include graph, so module k's
              transitive closure has k entries and every call site resolves through one.

  flat        the same N modules with none including another: every closure is one deep, and the
              only long list belongs to the root. Against `modules` this says whether the cost is
              the DEPTH of the graph or the number of lookups through it.

  instances   N distinct struct types through one generic. Grows monomorphization, which is a
              fixpoint that re-walks the page each round.

Usage: gen_scaling.py <family> <n> <outdir>   (prints the line count it generated)
"""
import sys
from pathlib import Path


def functions(n, d):
    # A chain: main calls f0, f0 calls f1, and so on, so every function is reachable. The arithmetic
    # differs per function, so no two are identical and nothing can fold them together.
    out = ["#include <stdlib::io>", ""]
    for i in range(n):
        nxt = "f{}(x + {})".format(i + 1, i % 7) if i + 1 < n else "x"
        out.append("local f{} x:long -> long {{ y: long = x * {} + {}; return {} + y; }}"
                   .format(i, 2 + i % 5, i, nxt))
    out.append("")
    out.append('main -> int { println("{}", f0(1)); return 0; }')
    write(d / "prog.k", out)


def modules(n, d):
    write(d / "package.kiln", ["package scale;"])
    for i in range(n):
        body = ["#include <m{}>".format(i - 1)] if i else []
        prev = "g{}(x)".format(i - 1) if i else "x"
        body.append("pub g{} x:long -> long {{ return {} + {}; }}".format(i, prev, i))
        write(d / "m{}.k".format(i), body)
    write(d / "prog.k", ["#include <stdlib::io>", "#include <m{}>".format(n - 1), "",
                         'main -> int { println("{}", g' + str(n - 1) + '(1)); return 0; }'])


def flat(n, d):
    # The root's calls go through helpers of twenty rather than one N-term expression: a single
    # 1600-term expression overflows the parser's recursive descent, which is a real limit worth
    # knowing and not the thing being measured here.
    write(d / "package.kiln", ["package scale;"])
    for i in range(n):
        write(d / "m{}.k".format(i), ["pub g{} x:long -> long {{ return x + {}; }}".format(i, i)])
    out = ["#include <stdlib::io>"]
    out += ["#include <m{}>".format(i) for i in range(n)]
    out.append("")
    per = 20
    for h in range(0, n, per):
        terms = " + ".join("g{}(1)".format(i) for i in range(h, min(h + per, n)))
        out.append("local h{} -> long {{ return {}; }}".format(h, terms))
    calls = " + ".join("h{}()".format(h) for h in range(0, n, per))
    out += ["", 'main -> int { println("{}", ' + calls + "); return 0; }"]
    write(d / "prog.k", out)


def instances(n, d):
    out = ["#include <stdlib::io>", "#include <stdlib::vec>", ""]
    out += ["struct S{} {{ a: long, b: long }}".format(i) for i in range(n)]
    out.append("")
    for i in range(n):
        out.append("local use{0} -> long {{ v: Vec<S{0}> = vec![]; v.push(S{0} {{ a: {0}, b: 1 }}); return v.len(); }}"
                   .format(i))
    out += ["", "main -> int {", "    t: long = 0;"]
    out += ["    t = t + use{}();".format(i) for i in range(n)]
    out += ['    println("{}", t); return 0;', "}"]
    write(d / "prog.k", out)


def write(path, lines):
    path.write_text("\n".join(lines) + "\n")


FAMILIES = {"functions": functions, "modules": modules, "flat": flat, "instances": instances}

if __name__ == "__main__":
    fam, n, outdir = sys.argv[1], int(sys.argv[2]), Path(sys.argv[3])
    outdir.mkdir(parents=True, exist_ok=True)
    for f in outdir.glob("*.k"):
        f.unlink()
    FAMILIES[fam](n, outdir)
    print(sum(1 for f in outdir.glob("*.k") for _ in f.open()))
