#!/bin/bash
# The seed builds gen1. Run from the repository root.
set -e
OUT=${1:-build}
mkdir -p "$OUT"
./bootstrap/kilnc main.k -o "$OUT/gen1.s"
# NASM's default multipass branch shortening (-Ox) took 690 s and 2.7 GB on this compiler's own
# text; -O1 takes four seconds. The compiler sizes its jumps itself (6-codegen/relax.k writes
# `short` where a jump reaches), so -O1 loses nothing to it.
nasm -O1 -felf64 "$OUT/gen1.s" -o "$OUT/gen1.o"
ld "$OUT/gen1.o" -o "$OUT/gen1"
echo "built $OUT/gen1 ($(wc -l < "$OUT/gen1.s") lines of assembly)"
