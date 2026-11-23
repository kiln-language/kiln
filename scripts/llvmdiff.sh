#!/bin/bash
# Runs the corpus through both back ends and checks that each program prints the same output and
# exits with the same code, or says which stage failed. The native path is the oracle. `$1` is a
# stride, so `5` checks every fifth program.
#
# Output is compared byte for byte. NUL bytes are dropped from both sides only because bash
# cannot hold one in a variable, not to make the comparison lenient.
cd "$(dirname "$0")/.."
# The exit code compared is the program's, not `tr`'s at the end of the pipe that captures its output.
set -o pipefail
./bootstrap/kilnc main.k -o /tmp/cd.s > /dev/null
nasm -O1 -felf64 /tmp/cd.s -o /tmp/cd.o
ld /tmp/cd.o -o /tmp/cd
C=/tmp/cd
D=/tmp/cdw; rm -rf $D; mkdir -p $D
cd ../Kiln

STRIDE=${1:-1}
agree=0; badas=0; badclang=0; differ=0; nonative=0
: > /tmp/cdfail.txt
for f in $(find tests -name '*.k' ! -name '*_member.k' | grep -Eiv 'err|error' | sort | awk -v s="$STRIDE" 'NR % s == 0'); do
    $C "$f" -o $D/n.s > /dev/null 2>&1 || { nonative=$((nonative + 1)); continue; }
    nasm -O1 -felf64 $D/n.s -o $D/n.o 2>/dev/null && ld $D/n.o -o $D/native 2>/dev/null \
        || { nonative=$((nonative + 1)); continue; }
    nout=$(timeout 10 "$D/native" 2>&1 | tr -d '\000'); nrc=$?

    $C "$f" --emit=llvm -o /dev/null > $D/p.ll 2>$D/e \
        || { badas=$((badas + 1)); echo "emit  $f" >> /tmp/cdfail.txt; continue; }
    if ! llvm-as $D/p.ll -o $D/p.bc 2>$D/e; then
        badas=$((badas + 1)); echo "as    $f: $(head -c 90 $D/e | tr -d '\n')" >> /tmp/cdfail.txt; continue
    fi
    if ! clang -O2 -w -nostdlib -static -no-pie -o $D/llvm $D/p.ll 2>$D/e; then
        badclang=$((badclang + 1)); echo "clang $f: $(head -c 90 $D/e | tr -d '\n')" >> /tmp/cdfail.txt; continue
    fi
    lout=$(timeout 10 "$D/llvm" 2>&1 | tr -d '\000'); lrc=$?

    if [ "$nout" = "$lout" ] && [ "$nrc" = "$lrc" ]; then
        agree=$((agree + 1))
    else
        differ=$((differ + 1))
        echo "run   $f: rc native=$nrc llvm=$lrc" >> /tmp/cdfail.txt
    fi
done
echo "agree: $agree   invalid IR: $badas   clang failed: $badclang   ran differently: $differ   native skipped: $nonative"
echo
echo "by stage:"
cut -d' ' -f1 /tmp/cdfail.txt | sort | uniq -c
echo
echo "first failures:"
head -10 /tmp/cdfail.txt
