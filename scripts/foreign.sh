#!/bin/bash
# Links a Kiln program with a foreign object (`selftests/foreign/`) that clobbers every register
# System V lets a callee clobber. Floats that are live across a call to a bodyless function, made
# directly or through a fn value, must come back intact. Run from the repository root and pass the
# compiler as $1.
C=${1:-build/gen1}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
F=selftests/foreign
"$C" $F/xmm_foreign.k -o "$T/a.s" || { echo "foreign      FAIL: did not compile"; exit 1; }
nasm -O1 -felf64 "$T/a.s" -o "$T/a.o" && nasm -felf64 $F/xmm_clobber.asm -o "$T/c.o" && ld "$T/a.o" "$T/c.o" -o "$T/a" \
    || { echo "foreign      FAIL: did not link"; exit 1; }
"$T/a"; rc=$?
if [ $rc = 0 ]; then echo "foreign      pass"; else echo "foreign      FAIL: exit $rc"; exit 1; fi
