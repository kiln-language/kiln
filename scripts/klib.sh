#!/bin/bash
# Package builds: `kilnc build`, the `.klib` cache, and code compiled against a `.klib`.
#
#   scripts/klib.sh [compiler] [--self] [--corpus]
#
# Always: a three-package program (util <- mid <- app, every one on stdlib) built into a scratch
# cache, and the cache held to what it promises --
#   fresh       a second build compiles nothing and does not relink
#   change      editing util rebuilds util, mid and app, and leaves stdlib alone
#   behaviour   a changed value in util reaches the program, through two packages, including as
#               the length of a template instance mid stamps (`Ring<long, nums::BASE>`)
#   leaf        editing app rebuilds app alone
#   foreign     a cached archive of another format is rebuilt, not trusted
#   damaged     a cached archive that is not one at all is rebuilt
#   stale       loading a .klib beside one built against an older version of it is refused
#   refused     a compile handed a foreign-format .klib refuses it
#   corrupt     a compile handed a .klib whose body was changed refuses it (the header hashes the body)
#   parsed      a dependent parses its own module and none of its dependencies' (it reads them parsed)
#   diamond     two packages on one base, both stamping Vec<long>, a tuple, a fn type and base's generic,
#               under a third that uses both: built, linked, run
#   tuples      a dependency's tuples (an owning element, a generic one, a Vec of them) destructured
#               two packages up, each element released once
#   methods     a dependency's methods with type parameters of their own, and a sum type's static
#               method, stamped and called by the dependent
#   stems       two packages that each have a module `util` declaring `util::Foo` are refused by name
#   reuse       a diamond's two sides each compile Vec<Item> and export it; the top links to the
#               first's and compiles none of it
#   fingerprint an instance compiled without a Drop the top sees is not reused; one compiled with it is
#   inline      a dependency's small functions are inlined from the IR its .klib carries, and a
#               bounds check through one is removed
#   positions   a refusal in a dependency's generic body, for a dependent's instance, names the
#               dependency's file and line
# --self:   the compiler's own tree built with `kilnc build`, and the result shown to compile
#           main.k to exactly the assembly the whole-program compiler does
# --corpus: every corpus program compiled as a package against stdlib.klib, run, and its output
#           compared with the whole-program build's (scripts/outputs.sh)
#
# Run from the repository root.
set -u
OUT=build
C=""
SELF=0; CORPUS=0
for a in "$@"; do
    case "$a" in
        --self) SELF=1 ;;
        --corpus) CORPUS=1 ;;
        *) C=$a ;;
    esac
done
if [ -z "$C" ]; then scripts/build.sh "$OUT" >/dev/null || exit 1; C=$OUT/gen1; fi
C=$(cd "$(dirname "$C")" && pwd)/$(basename "$C")
ROOT=$(pwd)
W=$OUT/klibtest
rm -rf "$W"; mkdir -p "$W/util" "$W/mid" "$W/app"
CACHE=$W/cache
fails=0
failed=""
ok()   { echo "  ok    $1"; }
bad()  { echo "  FAIL  $1"; fails=$((fails+1)); failed="$failed
    - $1"; }
# The package lines of a build's report, as "built:util,built:mid,..." for comparing.
summary() { grep -E '^  (built|fresh) ' | grep -v '(linked)' | awk '{print $1":"$2}' | tr '\n' ',' ; }

cat > "$W/util/package.kiln" <<'EOF'
package util;
EOF
cat > "$W/util/nums.k" <<'EOF'
#include <stdlib::vec>
pub BASE: long = 40;
pub table -> Vec<long> { return vec![1, 2, 3]; }
pub bump x:long -> long { return x + BASE; }
// A template with a length parameter, crossing the package boundary: util stamps the default
// instance itself, mid stamps one at util's constant.
pub struct Ring<T, N: long = 4> { v: [T; N], n: long }
methods Ring<T: Copy, N> {
    cap &self -> long { return N; }
    push &self x:T -> void { self.v[self.n % N] = x; self.n = self.n + 1; }
}
pub ringOf<T: Copy, N: long> -> Ring<T, N> { return Ring { n: 0 }; }
pub small -> Ring<long> { r: Ring<long> = ringOf(); r.push(1); return r; }
EOF
cat > "$W/mid/package.kiln" <<'EOF'
package mid;
depend util ../util
EOF
cat > "$W/mid/twice.k" <<'EOF'
#include <util::nums>
#include <stdlib::vec>
pub TWICE: long = BASE * 2;
pub sumTable -> long { t: Vec<long> = table(); s: long = 0; i: long = 0; while (i < t.len()) { s = s + t.get(i); i = i + 1; } return s; }
pub twice x:long -> long { return bump(x) * 2; }
pub ringCap -> long { r: Ring<long, nums::BASE> = ringOf(); r.push(7); return r.cap() + small().cap(); }
EOF
cat > "$W/app/package.kiln" <<'EOF'
package app;
depend mid ../mid
EOF
cat > "$W/app/main.k" <<'EOF'
#include <mid::twice>
#include <stdlib::io>
main -> int {
    println("{} {} {} {}", twice(1), TWICE, sumTable(), ringCap());
    return 0;
}
EOF

build() { "$C" build "$W/app" --cache "$CACHE" -o "$W/app.bin" 2>&1; }

echo "klib cache:"
r=$(build); s=$(echo "$r" | summary)
[ "$s" = "built:stdlib,built:util,built:mid,built:app," ] && ok "first build compiles all four" || { bad "first build: $s"; echo "$r"; }
[ "$("$W/app.bin")" = "82 80 6 44" ] && ok "the program runs: 82 80 6 44" || bad "program printed: $("$W/app.bin")"

r=$(build); s=$(echo "$r" | summary)
[ "$s" = "fresh:stdlib,fresh:util,fresh:mid,fresh:app," ] && echo "$r" | grep -q "(linked)" && ok "fresh: nothing compiled, nothing linked" || { bad "no-op build: $s"; echo "$r"; }

# Storage exists once: each global is defined by its own package's object and no other, and the
# allocator's shared state by the standard library's alone. A second copy would link fine and be
# a second heap.
dups=$(for k in "$CACHE"/*.klib; do nm --defined-only "$k" 2>/dev/null; done | awk '$2 ~ /^[DdBbRr]$/ && ($3 ~ /^gbl_/ || $3 == "__heapCentral") {print $3}' | sort | uniq -d)
heap=$(for k in "$CACHE"/*.klib; do nm --defined-only "$k" 2>/dev/null; done | grep -c ' __heapCentral$')
[ -z "$dups" ] && [ "$heap" = 1 ] && ok "storage: every global defined by one object, the heap's state by stdlib's alone" \
    || bad "storage defined twice: ${dups:-none}; __heapCentral defined $heap time(s)"
own=$(nm --defined-only "$CACHE/app.klib" 2>/dev/null | grep -c ' gbl_nums\$\| gbl_twice\$')
[ "$own" = 0 ] && ok "storage: app's object defines none of util's or mid's globals" || bad "app defines $own of its dependencies' globals"

echo "// a comment changes the bytes, not the meaning" >> "$W/util/nums.k"
r=$(build); s=$(echo "$r" | summary)
[ "$s" = "fresh:stdlib,built:util,built:mid,built:app," ] && ok "change: util, mid and app rebuilt, stdlib fresh" || { bad "after editing util: $s"; echo "$r"; }

cp "$CACHE/mid.klib" "$W/mid-old.klib"
sed -i 's/pub BASE: long = 40;/pub BASE: long = 50;/' "$W/util/nums.k"
r=$(build); s=$(echo "$r" | summary)
[ "$("$W/app.bin")" = "102 100 6 54" ] && ok "behaviour: a value changed in util reaches app, a template's length too (102 100 6 54)" || bad "after changing BASE the program printed: $("$W/app.bin")"

echo "// app only" >> "$W/app/main.k"
r=$(build); s=$(echo "$r" | summary)
[ "$s" = "fresh:stdlib,fresh:util,fresh:mid,built:app," ] && ok "leaf: app alone rebuilt" || { bad "after editing app: $s"; echo "$r"; }

# A dependent reads its dependencies' modules out of their .klibs already parsed: compiling app
# parses app's one module and nothing else.
msg=$("$C" --klib "$W/app/main.k" --extern stdlib="$CACHE/stdlib.klib" --extern util="$CACHE/util.klib" \
      --extern mid="$CACHE/mid.klib" -o "$W/x.s" --time-phases 2>&1)
echo "$msg" | grep -q "(1 modules parsed, [1-9][0-9]* read from a .klib" && ok "parsed: a dependent parses its own module and none of its dependencies'" \
    || bad "a dependency's module was parsed: $(echo "$msg" | grep 'modules parsed')"

# An archive whose metadata says another format: same bytes otherwise, so only the version line
# can be what refuses it. The body is binary, so the digit is patched in place.
T=$(mktemp -d)
(cd "$T" && ar x "$ROOT/$CACHE/util.klib" kiln.meta && printf 0 | dd of=kiln.meta bs=1 seek=10 count=1 conv=notrunc 2>/dev/null \
    && head -c 12 kiln.meta | grep -q "^kiln-klib 0" && ar rcsD foreign.klib kiln.meta)
# And one whose body has a byte changed: the header is intact, the hash it gives is not the body's.
(cd "$T" && mkdir c && cd c && ar x "$ROOT/$CACHE/util.klib" kiln.meta && n=$(stat -c%s kiln.meta) \
    && printf '\377' | dd of=kiln.meta bs=1 seek=$((n - 3)) count=1 conv=notrunc 2>/dev/null && ar rcsD ../corrupt.klib kiln.meta)
cp "$T/foreign.klib" "$CACHE/util.klib"
r=$(build); s=$(echo "$r" | summary)
echo "$s" | grep -q "built:util" && ok "foreign: a cached archive of another format is rebuilt" || { bad "foreign-format archive was trusted: $s"; echo "$r"; }

echo "not an archive" > "$CACHE/mid.klib"
r=$(build); s=$(echo "$r" | summary)
echo "$s" | grep -q "built:mid" && ok "damaged: a cached file that is no archive is rebuilt" || { bad "damaged archive was trusted: $s"; echo "$r"; }

# mid-old.klib was built against the util of before the BASE change; loading it beside today's
# util is the inconsistency the recorded dependency keys exist to catch.
msg=$("$C" --klib "$W/app/main.k" --extern stdlib="$CACHE/stdlib.klib" --extern util="$CACHE/util.klib" \
      --extern mid="$W/mid-old.klib" -o "$T/x.s" 2>&1)
echo "$msg" | grep -q "stale" && ok "stale: a .klib built against an older dependency is refused" || bad "stale archive accepted: $msg"

msg=$("$C" --klib "$W/app/main.k" --extern stdlib="$CACHE/stdlib.klib" --extern util="$T/foreign.klib" \
      --extern mid="$CACHE/mid.klib" -o "$T/x.s" 2>&1)
echo "$msg" | grep -q "is not a kiln-klib 4 archive" && ok "refused: a compile handed a foreign-format .klib refuses it" || bad "foreign archive accepted: $msg"

msg=$("$C" --klib "$W/app/main.k" --extern stdlib="$CACHE/stdlib.klib" --extern util="$T/corrupt.klib" \
      --extern mid="$CACHE/mid.klib" -o "$T/x.s" 2>&1)
echo "$msg" | grep -q "damaged .klib metadata" && ok "corrupt: a .klib whose body was changed is refused" || bad "corrupt archive accepted: $msg"
rm -rf "$T"

# A diamond: left and right each build on base and use the same instances (Vec<long>, a tuple, a
# function type, base's own generic), and top uses both. Each package stamps its own copies; the
# program links and runs.
mkdir -p "$W/base" "$W/left" "$W/right" "$W/top"
printf 'package base;\n' > "$W/base/package.kiln"
cat > "$W/base/shapes.k" <<'EOF'
#include <stdlib::vec>
pub struct Pair<T> { a: T, b: T }
pub pairOf<T: Copy> a:T b:T -> Pair<T> { return Pair { a: a, b: b }; }
pub total v:Vec<long> -> long { s: long = 0; i: long = 0; while (i < v.len()) { s = s + v.get(i); i = i + 1; } return s; }
EOF
printf 'package left;\ndepend base ../base\n' > "$W/left/package.kiln"
cat > "$W/left/l.k" <<'EOF'
#include <base::shapes>
#include <stdlib::vec>
local twice x:long -> long { return x * 2; }
local fourFive -> (long, long) { return (4, 5); }
pub leftSum -> long {
    v: Vec<long> = vec![1, 2, 3];
    q, r = fourFive();
    f: fn(long) -> long = &twice;
    p: Pair<long> = pairOf(6 as long, 7 as long);
    return total(v) + q + r + f(10) + p.a + p.b;
}
EOF
printf 'package right;\ndepend base ../base\n' > "$W/right/package.kiln"
cat > "$W/right/r.k" <<'EOF'
#include <base::shapes>
#include <stdlib::vec>
local thrice x:long -> long { return x * 3; }
local oneTwo -> (long, long) { return (1, 2); }
pub rightSum -> long {
    v: Vec<long> = vec![10, 20];
    q, r = oneTwo();
    f: fn(long) -> long = &thrice;
    p: Pair<long> = pairOf(3 as long, 4 as long);
    return total(v) + q + r + f(10) + p.a + p.b;
}
EOF
printf 'package top;\ndepend base ../base\ndepend left ../left\ndepend right ../right\n' > "$W/top/package.kiln"
cat > "$W/top/main.k" <<'EOF'
#include <left::l>
#include <right::r>
#include <base::shapes>
#include <stdlib::io>
#include <stdlib::vec>
main -> int {
    v: Vec<long> = vec![100];
    p: Pair<long> = pairOf(1 as long, 1 as long);
    println("{} {} {}", leftSum(), rightSum(), total(v) + p.a + p.b);
    return 0;
}
EOF
r=$("$C" build "$W/top" --cache "$CACHE" -o "$W/top.bin" 2>&1)
[ "$("$W/top.bin" 2>&1)" = "48 70 102" ] && ok "diamond: two packages on one base, sharing its instances, link and run (48 70 102)" \
    || { bad "diamond printed: $("$W/top.bin" 2>&1)"; echo "$r"; }

# Instances reused, not compiled again: base declares Item, which nothing below stamps a Vec of;
# left and right each stamp Vec<Item> first and export what they compiled under their own name;
# top, built on both, links to left's (the first in dependency order) and defines none of its own.
mkdir -p "$W/ibase" "$W/ileft" "$W/iright" "$W/itop"
printf 'package ibase;\n' > "$W/ibase/package.kiln"
printf '#include <stdlib::vec>\npub struct Item { n: long }\npub item n:long -> Item { return Item { n: n }; }\n' > "$W/ibase/item.k"
printf 'package ileft;\ndepend ibase ../ibase\n' > "$W/ileft/package.kiln"
printf '#include <ibase::item>\n#include <stdlib::vec>\npub leftItems -> long { v: Vec<Item>; v.push(item(3)); v.push(item(4)); return v.get(0).n + v.get(1).n + v.len(); }\n' > "$W/ileft/l.k"
printf 'package iright;\ndepend ibase ../ibase\n' > "$W/iright/package.kiln"
printf '#include <ibase::item>\n#include <stdlib::vec>\npub rightItems -> long { v: Vec<Item>; v.push(item(10)); return v.get(0).n * v.len(); }\n' > "$W/iright/r.k"
printf 'package itop;\ndepend ibase ../ibase\ndepend ileft ../ileft\ndepend iright ../iright\n' > "$W/itop/package.kiln"
printf '#include <ileft::l>\n#include <iright::r>\n#include <ibase::item>\n#include <stdlib::{io, vec}>\nmain -> int { v: Vec<Item>; v.push(item(100)); v.push(item(1)); println("{} {} {}", leftItems(), rightItems(), v.get(0).n + v.get(1).n + v.len()); return 0; }\n' > "$W/itop/main.k"
r=$("$C" build "$W/itop" --cache "$CACHE" -o "$W/itop.bin" 2>&1)
out=$("$W/itop.bin" 2>&1)
pl=$(nm "$CACHE/ileft.klib" 2>/dev/null | grep -c ' T .*RawVec_item\$Item_reserve\$\$ileft$')
pr=$(nm "$CACHE/iright.klib" 2>/dev/null | grep -c ' T .*RawVec_item\$Item_reserve\$\$iright$')
tu=$(nm "$CACHE/itop.klib" 2>/dev/null | grep -c ' U .*RawVec_item\$Item_reserve\$\$ileft$')
td=$(nm "$CACHE/itop.klib" 2>/dev/null | grep -c ' [Tt] .*RawVec_item\$Item_reserve$')
[ "$out" = "9 10 103" ] && [ "$pl" = 1 ] && [ "$pr" = 1 ] && [ "$tu" = 1 ] && [ "$td" = 0 ] \
    && ok "reuse: a diamond's two sides each export Vec<Item>; the top links to the first's and compiles none (9 10 103)" \
    || { bad "reuse: printed '$out'; left exports $pl, right $pr; top references left's $tu time(s), defines its own $td (RawVec<Item>.reserve)"; echo "$r"; }

# ...but not when the top sees an implementation the first side did not: fright implements Drop
# for fbase's Res, which fleft never saw, so fleft's Vec<Res>.set (which releases what it
# replaces) is not the one the top may run. It links to fright's, compiled against the same Drop.
mkdir -p "$W/fbase" "$W/fleft" "$W/fright" "$W/ftop"
printf 'package fbase;\n' > "$W/fbase/package.kiln"
printf '#include <stdlib::vec>\npub struct Res { id: long }\npub var gGone: long = 0;\n' > "$W/fbase/res.k"
printf 'package fleft;\ndepend fbase ../fbase\n' > "$W/fleft/package.kiln"
printf '#include <fbase::res>\n#include <stdlib::vec>\npub leftRes -> long { v: Vec<Res>; v.push(Res { id: 1 }); v.set(0, Res { id: 2 }); return v.len(); }\n' > "$W/fleft/l.k"
printf 'package fright;\ndepend fbase ../fbase\n' > "$W/fright/package.kiln"
printf '#include <fbase::res>\n#include <stdlib::{core, vec}>\nmethods Res for Drop { drop &self -> void { gGone = gGone + self.id; } }\npub rightRes -> long { v: Vec<Res>; v.push(Res { id: 5 }); v.set(0, Res { id: 6 }); return v.len(); }\n' > "$W/fright/r.k"
printf 'package ftop;\ndepend fbase ../fbase\ndepend fleft ../fleft\ndepend fright ../fright\n' > "$W/ftop/package.kiln"
printf '#include <fleft::l>\n#include <fright::r>\n#include <fbase::res>\n#include <stdlib::{io, vec}>\nmain -> int { rightRes(); before: long = gGone; v: Vec<Res>; v.push(Res { id: 100 }); v.set(0, Res { id: 1000 }); println("{} {}", before, gGone - before); return 0; }\n' > "$W/ftop/main.k"
r=$("$C" build "$W/ftop" --cache "$CACHE" -o "$W/ftop.bin" 2>&1)
out=$("$W/ftop.bin" 2>&1)
fl=$(nm "$CACHE/ftop.klib" 2>/dev/null | grep -c 'Vec_res\$Res_set\$\$fleft$')
fr=$(nm "$CACHE/ftop.klib" 2>/dev/null | grep -c ' U .*Vec_res\$Res_set\$\$fright$')
le=$(nm "$CACHE/fleft.klib" 2>/dev/null | grep -c ' T .*Vec_res\$Res_set\$\$fleft$')
[ "$out" = "11 100" ] && [ "$le" = 1 ] && [ "$fl" = 0 ] && [ "$fr" = 1 ] \
    && ok "fingerprint: an instance compiled without an implementation the top sees is not reused; the one compiled with it is (11 100)" \
    || { bad "fingerprint: printed '$out'; fleft exports set $le time(s); top references fleft's set $fl time(s), fright's $fr"; echo "$r"; }

# Inlining across packages: ilib's small functions travel as IR in its .klib, and iapp's inliner
# copies them, so no call into ilib is left in iapp's code; flow.k then removes the bounds check
# of a counted loop through ilib's checked accessor, as it would in a whole-program build.
mkdir -p "$W/ilib" "$W/iapp"
printf 'package ilib;\n' > "$W/ilib/package.kiln"
cat > "$W/ilib/il.k" <<'EOF'
#include <stdlib::panic>
pub struct Box2 { a: long, b: long }
pub triple x:long -> long { return x * 3 + 1; }
pub sumOf p:Box2 -> long { return p.a + p.b; }
pub at3 p:*long n:long i:long -> long { if (i < 0 || i >= n) { panicIndex("at3", i, n); } unsafe { return p[i]; } }
EOF
printf 'package iapp;\ndepend ilib ../ilib\n' > "$W/iapp/package.kiln"
cat > "$W/iapp/main.k" <<'EOF'
#include <ilib::il>
#include <stdlib::{io, heap}>
main -> int {
    s: long = 0;
    p: *long;
    unsafe { p = malloc(800) as *long; }
    for i in 0..100 { unsafe { p[i] = i; } }
    for i in 0..1000 { s = s + triple(i); }
    for i in 0..100 { s = s + at3(p, 100, i); }
    s = s + sumOf(Box2 { a: 5, b: 6 });
    println("{}", s);
    return 0;
}
EOF
r=$("$C" build "$W/iapp" --cache "$CACHE" -o "$W/iapp.bin" 2>&1)
out=$("$W/iapp.bin" 2>&1)
"$C" --klib "$W/iapp/main.k" --extern stdlib="$CACHE/stdlib.klib" --extern ilib="$CACHE/ilib.klib" -o "$W/iapp.s" 2>/dev/null
calls=$(grep -c 'call mfn_il\$' "$W/iapp.s")
checks=$(grep -c 'panicIndex' "$W/iapp.s")
[ "$out" = "1504461" ] && [ "$calls" = 0 ] && [ "$checks" = 0 ] \
    && ok "inline: a dependency's small functions are inlined from its .klib's IR, and a bounds check through one removed (1504461)" \
    || { bad "inline: printed '$out'; $calls call(s) into ilib left, $checks bounds check reference(s)"; echo "$r"; }

# Tuples across packages: a dependency's function returns a tuple holding its own Drop type and a
# String, its generic builds one, and a middle package returns tuples and a Vec of them; the top
# package destructures them. A tuple is named by its elements, so every package spells the same
# tuple the same way, and each element is released exactly once.
mkdir -p "$W/tbase" "$W/tmid" "$W/ttop"
printf 'package tbase;\n' > "$W/tbase/package.kiln"
cat > "$W/tbase/t.k" <<'EOF'
#include <stdlib::vec>
#include <stdlib::string>
pub var gFreed: long = 0;
pub struct Res { id: long }
methods Res for Drop { drop &self -> void { gFreed = gFreed + self.id; } }
pub open id:long -> (Res, String) { s: String = stringOf("r"); s.pushLong(id); return (Res { id: id }, s); }
pub swap<A, B> a:A b:B -> (B, A) { return (b, a); }
pub firsts v:Vec<(long, String)> -> long { t: long = 0; for p in v { t = t + p.0; } return t; }
EOF
printf 'package tmid;\ndepend tbase ../tbase\n' > "$W/tmid/package.kiln"
cat > "$W/tmid/m.k" <<'EOF'
#include <tbase::t>
#include <stdlib::vec>
#include <stdlib::string>
pub midOpen -> (Res, long) { r, s = open(5); return (r, s.len); }
pub midVec -> Vec<(long, String)> { v: Vec<(long, String)>; v.push((3, stringOf("x"))); v.push((4, stringOf("y"))); return v; }
EOF
printf 'package ttop;\ndepend tbase ../tbase\ndepend tmid ../tmid\n' > "$W/ttop/package.kiln"
cat > "$W/ttop/main.k" <<'EOF'
#include <tbase::t>
#include <tmid::m>
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::string>
main -> int {
    {
        r, n = midOpen();
        q, s = open(7);
        z: (long, Res) = swap(Res { id: 100 }, 9);
        v: Vec<(long, String)> = midVec();
        println("{} {} {} {} {} {} {}", r.id, n, q.id, s, z.0, z.1.id, firsts(v));
    }
    println("{}", gFreed);
    return 0;
}
EOF
r=$("$C" build "$W/ttop" --cache "$CACHE" -o "$W/ttop.bin" 2>&1)
[ "$("$W/ttop.bin" 2>&1 | tr '\n' ' ')" = "5 2 7 r7 9 100 7 112 " ] && ok "tuples: a dependency's tuples (an owning element, a generic one, a Vec of them) destructured in a dependent, each element released once" \
    || { bad "tuples printed: $("$W/ttop.bin" 2>&1)"; echo "$r"; }

# Methods with type parameters of their own, and a sum type's static method, declared in a
# dependency and stamped by the dependent: `&self` and static, in a plain block and in a
# `methods Vec<T>` block, and `Addr.parse(...)` on an enum with payloads.
mkdir -p "$W/gbase" "$W/gtop"
printf 'package gbase;\n' > "$W/gbase/package.kiln"
cat > "$W/gbase/b.k" <<'EOF'
#include <stdlib::vec>
#include <stdlib::option>
pub struct Box2 { n: long }
methods Box2 {
    pairWith<X> &self x:X -> (long, X) { return (self.n, x); }
    of<Y: Copy> y:Y -> (Y, Y) { return (y, y); }
}
pub enum Addr { V4(long), V6(long, long) }
methods Addr {
    parse n:long -> Option<Addr> { if (n < 0) { return Option.None; } return Option.Some(Addr.V4(n)); }
    port &self -> long { match self { V4(p) { return p; } V6(a, b) { return a + b; } } }
}
methods Vec<T> { firstAs<U> &self f:fn(T) -> U -> U { return f(self.get(0)); } }
EOF
printf 'package gtop;\ndepend gbase ../gbase\n' > "$W/gtop/package.kiln"
cat > "$W/gtop/main.k" <<'EOF'
#include <gbase::b>
#include <stdlib::io>
#include <stdlib::vec>
#include <stdlib::option>
sq x:long -> long { return x * x; }
main -> int {
    b: Box2 = Box2 { n: 4 };
    p: (long, str) = b.pairWith("hi");
    q: (long, long) = Box2.of(7 as long);
    a: Option<Addr> = Addr.parse(80);
    v: Vec<long> = vec![3, 2, 1];
    match a { Some(x) { println("{} {} {} {} {}", p.0, p.1, q.1, x.port(), v.firstAs(&sq)); } None { } }
    return 0;
}
EOF
r=$("$C" build "$W/gtop" --cache "$CACHE" -o "$W/gtop.bin" 2>&1)
[ "$("$W/gtop.bin" 2>&1)" = "4 hi 7 80 9" ] && ok "methods: a dependency's generic methods and a sum type's static method, stamped by the dependent" \
    || { bad "methods printed: $("$W/gtop.bin" 2>&1)"; echo "$r"; }

# Brace lists: `<multi::{alpha, beta}>` is two includes of package `multi`, and `<{alpha}>` one of
# a module's own package. Each module must reach the archive's module directory as an edge, or the
# dependent's compile cannot find what it reads from `multi.klib`.
mkdir -p "$W/multi" "$W/muse"
printf 'package multi;\n' > "$W/multi/package.kiln"
printf 'pub alphaOf x:long -> long { return x + 1; }\n' > "$W/multi/alpha.k"
printf '#include <{alpha}>\n#include <stdlib::{vec}>\npub betaOf x:long -> long { v: Vec<long>; v.push(alphaOf(x)); return v.get(0) * 2; }\n' > "$W/multi/beta.k"
printf 'package muse;\ndepend multi ../multi\n' > "$W/muse/package.kiln"
printf '#include <multi::{alpha, beta}>\n#include <stdlib::{io, vec}>\nmain -> int { println("{}", alphaOf(1) + betaOf(2)); return 0; }\n' > "$W/muse/main.k"
r=$("$C" build "$W/muse" --cache "$CACHE" -o "$W/muse.bin" 2>&1)
[ "$("$W/muse.bin" 2>&1)" = "8" ] && ok "brace lists: <multi::{alpha, beta}> and <{alpha}> include each module, through the .klib too (8)" \
    || { bad "brace-list build printed: $("$W/muse.bin" 2>&1)"; echo "$r"; }

# A distinct type crosses a .klib as what it is: `units` declares `Meters = distinct long` with an
# `Add` and a method; a dependent uses both, and is still refused a plain long where a Meters goes.
mkdir -p "$W/units" "$W/uuse" "$W/ubad"
printf 'package units;\n' > "$W/units/package.kiln"
printf '#include <stdlib::core>\npub type Meters = distinct long;\nmethods Meters for Add<Meters> { add self o:Meters -> Meters { return ((self as long) + (o as long)) as Meters; } }\nmethods Meters { km &self -> long { return (self as long) / 1000; } }\npub meters n:long -> Meters { return n as Meters; }\n' > "$W/units/m.k"
printf 'package uuse;\ndepend units ../units\n' > "$W/uuse/package.kiln"
printf '#include <units::m>\n#include <stdlib::io>\nmain -> int { d: Meters = meters(1500) + meters(2500); println("{}", d.km()); return 0; }\n' > "$W/uuse/main.k"
r=$("$C" build "$W/uuse" --cache "$CACHE" -o "$W/uuse.bin" 2>&1)
[ "$("$W/uuse.bin" 2>&1)" = "4" ] && ok "distinct: a dependent uses a .klib's distinct type, its Add and its method (4)" \
    || { bad "distinct build printed: $("$W/uuse.bin" 2>&1)"; echo "$r"; }
printf 'package ubad;\ndepend units ../units\n' > "$W/ubad/package.kiln"
printf '#include <units::m>\nmain -> int { d: Meters = 5; return d.km() as int; }\n' > "$W/ubad/main.k"
r=$("$C" build "$W/ubad" --cache "$CACHE" -o "$W/ubad.bin" 2>&1)
echo "$r" | grep -q "a distinct type converts only by" && ok "distinct: read from a .klib, it still converts only by \`as\`" \
    || bad "distinct from a .klib accepted a long: $r"

# Two packages that each have a module `util` declaring `util::Foo`: the module stem is the
# namespace, so the two collide, and the build says which packages.
mkdir -p "$W/one" "$W/two" "$W/both"
printf 'package one;\n' > "$W/one/package.kiln"
printf 'pub struct Foo { x: long }\npub oneX -> long { return 1; }\n' > "$W/one/util.k"
printf 'package two;\n' > "$W/two/package.kiln"
printf 'pub struct Foo { y: long }\npub twoY -> long { return 2; }\n' > "$W/two/util.k"
printf 'package both;\ndepend one ../one\ndepend two ../two\n' > "$W/both/package.kiln"
printf '#include <one::util>\n#include <two::util>\nmain -> int { return 0; }\n' > "$W/both/main.k"
r=$("$C" build "$W/both" --cache "$CACHE" -o "$W/both.bin" 2>&1)
echo "$r" | grep -q "declared by package 'one' and by package 'two'" && ok "stems: two packages each declaring util::Foo are refused, naming both" \
    || bad "two packages' util::Foo: $r"

# A dependency's generic body that is wrong only for the instance a dependent asks for: the
# refusal comes from the dependent's compile, and still names the dependency's file and line,
# which the .klib carries for every statement.
mkdir -p "$W/gdep" "$W/guse"
printf 'package gdep;\n' > "$W/gdep/package.kiln"
printf 'pub struct Holder<T> { v: T }\nmethods Holder<T> {\n    first &self -> long { return 1; }\n    twice &self -> long { s: str = self.v; return s.len * 2; }\n}\n' > "$W/gdep/shape.k"
printf 'package guse;\ndepend gdep ../gdep\n' > "$W/guse/package.kiln"
printf '#include <gdep::shape>\nmain -> int {\n    h: Holder<long> = Holder { v: 3 };\n    return h.twice() as int;\n}\n' > "$W/guse/main.k"
r=$("$C" build "$W/guse" --cache "$CACHE" -o "$W/guse.bin" 2>&1)
echo "$r" | grep -q "gdep/shape.k:4:[0-9]*: Error: " && ok "positions: a dependency's generic body refused for a dependent's instance names the dependency's file and line" \
    || bad "a refusal in a dependency's generic body: $r"

# hooks: `@init`/`@fini` in two packages run in order -- a dependency's start before its
# dependent's, the ends the other way round, stdout's flush (stdlib, read first) last of all --
# the same from a package build as from a whole-program compile, under the same symbols.
mkdir -p "$W/hdep" "$W/happ"
printf 'package hdep;\n' > "$W/hdep/package.kiln"
printf '#include <stdlib::io>\npub var gOrder: long = 0;\n@init startDep -> void { gOrder = gOrder * 10 + 1; }\n@fini endDep -> void { println("end dep"); }\n' > "$W/hdep/first.k"
printf 'package happ;\ndepend hdep ../hdep\n' > "$W/happ/package.kiln"
printf '#include <hdep::first>\n#include <stdlib::io>\nvar gMine: long = 0;\n@init startApp -> void { gMine = gOrder * 10 + 2; }\n@fini endApp -> void { println("end app"); }\nmain -> long { println("main {}", gMine); return 0; }\n' > "$W/happ/main.k"
want=$(printf 'main 12\nend app\nend dep')
r=$("$C" build "$W/happ" --cache "$CACHE" -o "$W/happ.bin" 2>&1); hp=$("$W/happ.bin" 2>&1)
"$C" "$W/happ/main.k" -o "$W/happ.s" >/dev/null 2>&1 && nasm -O1 -felf64 "$W/happ.s" -o "$W/happ.o" && ld "$W/happ.o" -o "$W/happw.bin" \
    && hw=$("$W/happw.bin" 2>&1) || hw="whole-program build failed"
syms() { nm "$1" 2>/dev/null | awk '{print $NF}' | grep -v '\.end' | grep -E '\$(startDep|startApp|endDep|endApp|heapInit|flush)$' | sort | tr '\n' ' '; }
[ "$hp" = "$want" ] && [ "$hw" = "$want" ] && [ "$(syms "$W/happ.bin")" = "$(syms "$W/happw.bin")" ] \
    && ok "hooks: @init/@fini across two packages run in order, the same built as packages and whole (symbols: $(syms "$W/happ.bin"))" \
    || bad "hooks: package build printed <$hp>, whole-program <$hw>, symbols <$(syms "$W/happ.bin")> vs <$(syms "$W/happw.bin")>"

if [ $SELF = 1 ]; then
    echo "the compiler built from packages:"
    t0=$(date +%s%N)
    "$C" build --cache "$OUT/klib" -o "$OUT/kiln" > "$W/self.log" 2>&1; st=$?
    tail -1 "$W/self.log"
    t1=$(date +%s%N)
    echo "  ($(( (t1 - t0) / 1000000 )) ms)"
    [ $st = 0 ] || { bad "kilnc build of the compiler failed (status $st)"; tail -20 "$W/self.log"; }
    # The executable must be at least as new as the compiler that built it and every source it
    # was built from: an old build/kiln left by a failed or skipped link would compare an old
    # compiler against this one.
    stale=$(find "$OUT/kiln" -maxdepth 0 ! -newer "$C" 2>/dev/null; find . \( -path ./build -o -path ./attic -o -path ./examples \) -prune -o \( -name '*.k' -o -name package.kiln \) -newer "$OUT/kiln" -print 2>/dev/null | head -3)
    [ -x "$OUT/kiln" ] && [ -z "$stale" ] && ok "build/kiln is newer than the compiler and every source" \
        || bad "build/kiln is missing or older than its inputs: ${stale:-missing}"
    "$C" main.k -o "$W/whole.s" && "$OUT/kiln" main.k -o "$W/fromklib.s" \
        && cmp -s "$W/whole.s" "$W/fromklib.s" \
        && ok "build/kiln compiles main.k to exactly what $(basename "$C") does" \
        || bad "build/kiln and $(basename "$C") disagree on main.k"
fi

if [ $CORPUS = 1 ]; then
    echo "the corpus against stdlib.klib:"
    "$C" build stdlib --cache "$OUT/klib" | tail -1
    STD=$ROOT/$OUT/klib/stdlib.klib
    scripts/outputs.sh "$C" "$ROOT/$W/out.whole" | sed 's/^/  /'
    E=$ROOT/$W/out.klib
    mkdir -p "$E"
    T=$(mktemp -d)
    n=0; skipped=0
    cd ../Kiln || exit 1
    for f in $(find tests -name '*.k' ! -name '*_member.k' | grep -Eiv 'err|error' | sort); do
        case "$f" in
            tests/control-flow/loop.k|tests/control-flow/control_flow.k|tests/functions/main_args.k) continue ;;
            tests/stdlib-heap/heap_basic.k|tests/stdlib-threads/thread_shared.k) continue ;;
            # Programs of several packages, which need their own dependencies' .klibs too.
            tests/packages/dep*) skipped=$((skipped+1)); continue ;;
        esac
        key=$(echo "$f" | tr '/' '_')
        if ! "$C" --klib "$f" --extern stdlib="$STD" -o "$T/o.s" >/dev/null 2>&1; then echo "BUILDFAIL" > "$E/$key"; n=$((n+1)); continue; fi
        if ! nasm -O1 -felf64 "$T/o.s" -o "$T/o.o" 2>/dev/null || ! ld --gc-sections -e _start "$T/o.o" print.o "$STD" -o "$T/o.bin" 2>/dev/null; then
            echo "LINKFAIL" > "$E/$key"; n=$((n+1)); continue
        fi
        timeout 10 "$T/o.bin" > "$E/$key" 2>&1
        echo "EXIT=$?" >> "$E/$key"
        n=$((n+1))
    done
    cd "$ROOT"
    rm -rf "$T"
    differ=0
    for g in "$E"/*; do
        k=$(basename "$g")
        cmp -s "$g" "$ROOT/$W/out.whole/$k" || { differ=$((differ+1)); echo "  differs: $k"; }
    done
    [ $differ = 0 ] && ok "$n programs print the same against stdlib.klib as whole-program ($skipped multi-package programs not run this way)" \
                    || bad "$differ of $n programs print something else against stdlib.klib"
fi

[ $fails = 0 ] && echo "klib: all checks passed" || { echo "klib: $fails check(s) FAILED:$failed"; exit 1; }
