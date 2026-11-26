#!/bin/bash
# How much of the corpus the LLVM path can emit, and what stops the rest.
cd "$(dirname "$0")/.."
./bootstrap/kilnc main.k -o /tmp/cv.s > /dev/null
nasm -O1 -felf64 /tmp/cv.s -o /tmp/cv.o
ld /tmp/cv.o -o /tmp/cv
cd ../Kiln
ok=0; bad=0
: > /tmp/reasons.txt
for f in $(find tests -name '*.k' ! -name '*_member.k' | grep -Eiv 'err|error' | sort); do
    if /tmp/cv "$f" --emit=llvm -o /dev/null > /tmp/cv.ll 2>/tmp/cv.err; then
        ok=$((ok+1))
    else
        bad=$((bad+1))
        sed -n 's/.*`--emit=llvm` cannot translate \(.*\) yet.*/\1/p' /tmp/cv.err >> /tmp/reasons.txt
        grep -q 'cannot translate' /tmp/cv.err || echo "(other) $(head -c 60 /tmp/cv.err)" >> /tmp/reasons.txt
    fi
done
echo "corpus programs the LLVM path emits: $ok    refused: $bad"
# The reasons are listed only when something was refused, or with VERBOSE=1.
if [ "$bad" != 0 ] || [ "${VERBOSE:-0}" = 1 ]; then
    echo
    echo "what stops the rest:"
    sort /tmp/reasons.txt | uniq -c | sort -rn | head -12
fi
