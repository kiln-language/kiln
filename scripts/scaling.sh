#!/bin/bash
# Does compile time grow with the program, or faster than it?
#
# Three families, one axis each (see gen_scaling.py). For each size the compiler is run three
# times and the fastest kept, then the ratio of time to size is printed: a LINEAR compiler holds
# that ratio flat as N grows, and a quadratic one doubles it every time N doubles. That ratio is
# the whole point of the table — the raw seconds say how big the program is, not how the compiler
# scales.
#
# Run from the repository root.
OUT=${2:-build}
C=${1:-$OUT/gen1}
[ -x "$C" ] || scripts/build.sh "$OUT" >/dev/null
C=$(cd "$(dirname "$C")" && pwd)/$(basename "$C")
GEN=$(pwd)/scripts/gen_scaling.py
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
ln -sfn "$(pwd)/stdlib" "$W/stdlib"

best() { m=999; for i in 1 2 3; do
    v=$( { /usr/bin/time -f "%e" "$@" >/dev/null; } 2>&1 | tail -1 )
    m=$(awk -v a="$v" -v b="$m" 'BEGIN{print (a<b)?a:b}'); done; echo "$m"; }

for fam in ${3:-functions modules flat instances}; do
    case $fam in
        functions) sizes="250 500 1000 2000 4000" ;;
        modules)   sizes="100 200 400 800 1600" ;;
        flat)      sizes="100 200 400 800 1600" ;;
        instances) sizes="10 20 40 80 160" ;;
    esac
    echo "== $fam =="
    printf "  %6s %8s %8s %10s %10s\n" N lines secs "us/line" "vs first"
    first=""
    for n in $sizes; do
        lines=$(python3 "$GEN" "$fam" "$n" "$W/src")
        ( cd "$W" && cp -f src/*.k . 2>/dev/null; cp -f src/package.kiln . 2>/dev/null || true )
        t=$(cd "$W" && best "$C" ./prog.k -o out.s)
        per=$(awk -v t="$t" -v l="$lines" 'BEGIN{printf "%.2f", (l>0)? t*1000000/l : 0}')
        [ -z "$first" ] && first=$per
        rel=$(awk -v a="$per" -v b="$first" 'BEGIN{printf "%.2fx", (b>0)? a/b : 0}')
        printf "  %6s %8s %8s %10s %10s\n" "$n" "$lines" "$t" "$per" "$rel"
        rm -f "$W"/*.k "$W"/package.kiln
    done
done
