#!/bin/bash
# gen1 builds gen2 builds gen3, and the last two must be byte-identical: the compiler has
# reached a fixpoint on its own source. Run from the repository root.
set -e
OUT=${1:-build}
[ -x "$OUT/gen1" ] || scripts/build.sh "$OUT"
"$OUT/gen1" main.k -o "$OUT/gen2.s"
nasm -O1 -felf64 "$OUT/gen2.s" -o "$OUT/gen2.o"; ld "$OUT/gen2.o" -o "$OUT/gen2"
"$OUT/gen2" main.k -o "$OUT/gen3.s"
if cmp -s "$OUT/gen2.s" "$OUT/gen3.s"; then
    echo "fixpoint holds: gen2.s == gen3.s"
else
    echo "FIXPOINT BROKEN"; diff "$OUT/gen2.s" "$OUT/gen3.s" | head -20; exit 1
fi
