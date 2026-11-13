#!/bin/bash
# The three suites this compiler is held to. Run from the repository root; pass the compiler to
# test as $1, or leave it and gen1 is built first.
#
#   selftests   — this tree's own tests. `expected.tsv` gives each one an exit code, or, for a
#                 program whose name says it must be REFUSED, a substring of the refusal.
#   corpus      — every program in ../Kiln/tests that must compile, and does.
#   rejections  — every program there whose name holds `err` or `error`, which must not.
OUT=${2:-build}
C=${1:-}
if [ -z "$C" ]; then scripts/build.sh "$OUT" >/dev/null; C=$OUT/gen1; fi
C=$(cd "$(dirname "$C")" && pwd)/$(basename "$C")
ROOT=$(pwd)
CORPUS=$ROOT/../Kiln
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT

pass=0; fail=0
while IFS=$(printf '\t') read -r name exp; do
    [ -z "$name" ] && continue
    out=$("$C" "selftests/$name.k" -o "$T/t.s" 2>&1); rc=$?
    case "$exp" in
        ""|*[!0-9]*)
            if [ $rc -eq 0 ]; then echo "  $name: expected refusal <$exp>, compiled"; fail=$((fail+1))
            elif echo "$out" | grep -qF "$exp"; then pass=$((pass+1))
            else echo "  $name: got: $out"; fail=$((fail+1)); fi ;;
        *)
            if [ $rc -ne 0 ]; then echo "  $name: compile failed: $out"; fail=$((fail+1)); continue; fi
            nasm -O1 -felf64 "$T/t.s" -o "$T/t.o" 2>/dev/null && ld "$T/t.o" -o "$T/t.bin" 2>/dev/null \
                || { echo "  $name: assemble/link failed"; fail=$((fail+1)); continue; }
            "$T/t.bin" >/dev/null 2>&1; got=$?
            if [ "$got" = "$exp" ]; then pass=$((pass+1)); else echo "  $name: exit $got, wanted $exp"; fail=$((fail+1)); fi ;;
    esac
done < selftests/expected.tsv
echo "selftests    pass=$pass fail=$fail"

[ -d "$CORPUS/tests" ] || { echo "corpus       (../Kiln/tests not present, skipped)"; exit 0; }
cd "$CORPUS" || exit 1
ok=0; bad=0
for f in $(find tests -name '*.k' ! -name '*_member.k' | grep -Eiv 'err|error' | sort); do
    if "$C" "$f" -o "$T/c.s" >"$T/c.err" 2>&1; then ok=$((ok+1))
    else bad=$((bad+1)); echo "  $f: $(head -1 "$T/c.err")"; fi
done
echo "corpus       build=$ok regressed=$bad"
ref=0; acc=0
for f in $(find tests -name '*.k' | grep -Ei 'err|error' | sort); do
    if "$C" "$f" -o "$T/e.s" >/dev/null 2>&1; then acc=$((acc+1)); echo "  $f: accepted, must be refused"
    else ref=$((ref+1)); fi
done
echo "rejections   refused=$ref wrongly-accepted=$acc"
