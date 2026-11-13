#!/bin/bash
# The seed builds gen1. Run from the repository root.
set -e
OUT=${1:-build}
mkdir -p "$OUT"
./bootstrap/kilnc main.k -o "$OUT/gen1.s"
# NASM's default multipass branch shortening takes minutes on a file this size; -O1 is one pass,
# assembles the same file in seconds, and the interleaved benchmark cannot tell the two apart.
nasm -O1 -felf64 "$OUT/gen1.s" -o "$OUT/gen1.o"
ld "$OUT/gen1.o" -o "$OUT/gen1"
echo "built $OUT/gen1 ($(wc -l < "$OUT/gen1.s") lines of assembly)"
