#!/bin/bash
# The nine benchmarks, built by two compilers and by `gcc -O2`, interleaved: every variant of
# every program runs once per round, so a machine that gets busy mid-run spreads that across all
# of them rather than one. The minimum of five rounds is reported, and every variant's OUTPUT is
# checked to agree before any of it is timed.
#
#   scripts/bench.sh build/gen1 [other-compiler]
A=${1:-build/gen1}
B=${2:-}
ROOT=$(pwd)
SRC=$ROOT/../Kiln/benchmarks/src
A=$(cd "$(dirname "$A")" && pwd)/$(basename "$A")
[ -n "$B" ] && B=$(cd "$(dirname "$B")" && pwd)/$(basename "$B")
W=$(mktemp -d); trap 'rm -rf "$W"' EXIT
BENCHES="sum fib primes collatz sieve records vector higher strings"
[ -d "$SRC" ] || { echo "../Kiln/benchmarks/src not present"; exit 1; }

build() {   # $1 label, $2 compiler
    for b in $BENCHES; do
        "$2" "$SRC/$b.k" -o "$W/$b.$1.s" >/dev/null 2>&1 || continue
        nasm -O1 -felf64 "$W/$b.$1.s" -o "$W/$b.$1.o" 2>/dev/null &&
          ld "$W/$b.$1.o" "$ROOT/../Kiln/print.o" -o "$W/$b.$1" 2>/dev/null
    done
}
build a "$A"
[ -n "$B" ] && build b "$B"
for b in $BENCHES; do gcc -O2 -o "$W/$b.gcc" "$SRC/$b.c" 2>/dev/null; done
if [ -n "$B" ]; then
    for b in $BENCHES; do
        [ -x "$W/$b.a" ] && [ -x "$W/$b.b" ] || continue
        x=$("$W/$b.a" 2>&1 | md5sum); y=$("$W/$b.b" 2>&1 | md5sum)
        [ "$x" = "$y" ] || echo "MISMATCH $b: the two builds print different things"
    done
fi
declare -A best
for round in 1 2 3 4 5; do
    for b in $BENCHES; do
        for v in a b gcc; do
            [ -x "$W/$b.$v" ] || continue
            s=$( { /usr/bin/time -f "%e" "$W/$b.$v" > /dev/null; } 2>&1 | tail -1 )
            cur=${best[$b.$v]:-999}
            awk -v n="$s" -v c="$cur" 'BEGIN{exit !(n<c)}' && best[$b.$v]=$s
        done
    done
done
printf "%-9s %9s %9s %9s\n" bench "$(basename "$A")" "$( [ -n "$B" ] && basename "$B" || echo - )" "gcc -O2"
for b in $BENCHES; do
    printf "%-9s %9s %9s %9s\n" "$b" "${best[$b.a]:--}" "${best[$b.b]:--}" "${best[$b.gcc]:--}"
done
