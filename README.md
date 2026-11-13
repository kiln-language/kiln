# Kiln

Kiln is a small systems programming language, and this repository is its compiler. The compiler
is written in Kiln and compiles itself.

It turns a program into x86-64 assembly (NASM syntax), which assembles and links into a static
Linux executable. Nothing sits underneath: no libc, no C runtime. The standard library in
`stdlib/` is written in Kiln as well, down to the heap allocator, threads and sockets, and it
talks to the kernel through `syscall`.

```k
#include <stdlib::{io, vec}>

enum Shape { Circle(long), Rect(long, long) }

area s:&Shape -> long {
    a: long = 0;
    match s {
        Circle(r) { a = 3 * r * r; }
        Rect(w, h) { a = w * h; }
    }
    return a;
}

addRects inout v:Vec<Shape> n:long -> void {
    for i in 1..n { v.push(Shape.Rect(i, i + 1)); }
}

main -> int {
    shapes: Vec<Shape> = vec![Shape.Circle(2)];
    addRects(&shapes, 4);
    total: long = 0;
    for s in shapes { total = total + area(s); }
    println("{} shapes, total area {}", shapes.len(), total);
    return 0;
}
```

```
$ build/gen1 shapes.k -o shapes.s
$ nasm -O1 -felf64 shapes.s -o shapes.o && ld shapes.o -o shapes
$ ./shapes
4 shapes, total area 32
```

That binary is 73 KB and has no dependencies.

## The language

- **Memory safety without a garbage collector or lifetime annotations.** Every value has one
  owner. A parameter is read-only, `inout` (changed in place, marked `&x` at the call), or a
  sink (the callee takes the value). Only `inout` is written out; the compiler works the other
  two out from the function body. Aliasing is checked per call, so there is no borrow-checker
  graph to satisfy. `unsafe` blocks are there for the cases the checker can't see through.
- **Sum types and `match`**, generics with trait bounds, operator traits, `?` on `Result` and
  `Option`, tuples and destructuring.
- **Compile-time evaluation.** A global's initializer runs inside the compiler and the result is
  written into the binary, heap blocks included: `PRIMES: Vec<long> = sieve(1000);` costs nothing
  at startup. Globals are immutable unless declared `var`.
- **Macros and derives written in Kiln.** A `macro` receives the syntax tree as an ordinary value
  (`stdlib::ast`) and returns a new one. `quote` builds trees, and a trait can supply its own
  `derive`.
- **Packages.** A folder with a `package.kiln` manifest is a package. `kilnc build` compiles each
  package once into a cached `.klib` and only rebuilds what changed.

## Building

You need Linux (WSL works fine) with `nasm` and `ld`. Run everything from the repository root:
the compiler looks for the standard library at the relative path `stdlib`.

```sh
scripts/build.sh      # bootstrap/kilnc compiles main.k into build/gen1
scripts/fixpoint.sh   # gen1 builds gen2, gen2 builds gen3, and gen2.s must equal gen3.s
scripts/gate.sh       # the self-tests
```

`build/gen1` is the compiler:

```sh
build/gen1 prog.k -o prog.s                      # compile one program
build/gen1 build path/to/package -o app          # build a package and its dependencies
build/gen1 prog.k --emit=ir                      # stop after a stage: pre, tokens, ast, typed, ir, llvm
build/gen1 --help                                # everything else
```

`gate.sh` runs the self-tests in `selftests/`, about 380 programs that each have to exit with a
given code or fail to compile with a given error. It has two more suites (a corpus of programs
that must compile, and one that must be rejected) that use a test corpus kept outside this
repository; without it, they're skipped.

## Bootstrapping

You need a Kiln compiler to build the Kiln compiler. `bootstrap/kilnc` is that seed: an earlier
build of this same source, checked in as a Linux binary next to `bootstrap/kilnc.s`, the assembly
it came from. If you'd rather not run a binary out of a repository, rebuild it from the assembly
first:

```sh
nasm -O1 -felf64 bootstrap/kilnc.s -o kilnc.o && ld kilnc.o -o bootstrap/kilnc
```

It behaves the same but may differ by a few bytes, depending on your NASM version.

The first seed was built by an older Kiln compiler written in C++, which is kept in
[kiln-bootstrap](https://github.com/kiln-language/kiln-bootstrap). Each seed since then is a
compiler this source produced that also passed the fixpoint check. A seed only gets replaced
when the compiler's own source starts using a feature the previous seed can't read.

## Layout

The phases run in folder order.

| Path | What's there |
|---|---|
| `0-support/` | Shared by every phase: the name interner, source text, compile-time float arithmetic |
| `1-cumulation/` | Follows `#include`s to collect the program's files; `kilnc build` and the `.klib` format |
| `2-preprocess/` | Package manifests and include resolution |
| `3-lex/` | The lexer |
| `4-parse/` | The parser, syntax tree, declaration registry and `quote` |
| `5-transform/` | Type checking and ownership, monomorphization, the compile-time evaluator |
| `6-codegen/` | The IR and its optimizer, register allocation, x86-64 output, and an experimental LLVM IR back end |
| `main.k` | The command-line driver |
| `stdlib/` | The standard library |
| `selftests/` | Test programs; `expected.tsv` gives each one's exit code or expected error |
| `scripts/` | Build, fixpoint, test, benchmark and package-cache checks |

The compiler is about 46,000 lines of Kiln, and the standard library another 9,600.

## License

The compiler is free software under the [GNU General Public License v3.0](LICENSE). The
standard library in `stdlib/` is under the [Mozilla Public License 2.0](stdlib/LICENSE).

In practice:

- **Programs you write in Kiln are yours.** You can keep them closed and sell them. The bits of
  the compiler that end up in its output are covered by an [exception](LICENSE-EXCEPTION), and
  the standard library code compiled into your program only asks that you tell people where its
  source can be found.
- **If you change a standard library file and ship it,** you publish that file.
- **If you distribute a modified compiler,** you publish its source under the GPL.
