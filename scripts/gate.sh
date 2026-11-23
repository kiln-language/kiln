#!/bin/bash
# Runs the test suites this compiler is held to. Run it from the repository root and pass the
# compiler to test as $1; without one, gen1 is built first.
#
#   selftests:   this tree's own tests. `expected.tsv` gives each one an exit code or, for a
#                program whose name says it must be REFUSED, a substring of the error it prints.
#                A refused one with a `.expect` file beside it must print exactly that file
#                (every error, and nothing else): the parser's tests of going on past errors.
#   rewind:      for each of those, `--verify-regops` holds the registry the parse left to the
#                one its operation log replays to, so a declaration taken back for an error took
#                all it had registered with it.
#   foreign:     a program linked with a foreign object (`scripts/foreign.sh`).
#   corpus:      every program in ../Kiln/tests that must compile, each of which has to.
#   rejections:  every program there whose name holds `err` or `error`, each of which must be
#                refused.
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
            elif [ -f "selftests/$name.expect" ]; then
                if [ "$out" = "$(cat "selftests/$name.expect")" ]; then pass=$((pass+1))
                else echo "  $name: printed other than $name.expect:"; echo "$out" | head -20 | sed 's/^/    /'; fail=$((fail+1)); fi
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
# The registry after a parse that took declarations back, against its log. A test that reaches
# the cap stops in the middle of the parse, before there is anything to compare.
rw=0; rwbad=0
for e in selftests/*.expect; do
    [ -f "$e" ] || continue
    grep -q "too many errors" "$e" && continue
    n=$(basename "$e" .expect)
    if "$C" --verify-regops "selftests/$n.k" 2>&1 | grep -q '; 0 differences$'; then rw=$((rw+1))
    else rwbad=$((rwbad+1)); echo "  $n: the registry after its errors is not the one its log replays to"; fi
done
echo "rewind       pass=$rw fail=$rwbad"
# A program linked with a foreign object that clobbers every register System V lets it clobber.
scripts/foreign.sh "$C"

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
