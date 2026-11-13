#!/bin/bash
# Record every corpus program's OUTPUT and exit code, so two builds of the compiler can be
# compared on what the programs they build actually print. Run from the repository root:
#
#   scripts/outputs.sh build/gen1 out.before
#   ...change the back end...
#   scripts/outputs.sh build/gen1 out.after
#   diff -rq out.before out.after
#
# This is the gate any change to lowering, the optimizer or the emitter has to pass. The other
# suites cannot see a miscompile: it builds, it links, and it prints the wrong thing.
C=$1
OUT=$2
[ -n "$OUT" ] || { echo "usage: scripts/outputs.sh <compiler> <output-dir>"; exit 1; }
C=$(cd "$(dirname "$C")" && pwd)/$(basename "$C")
ROOT=$(pwd)
CORPUS=$ROOT/../Kiln
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
rm -rf "$OUT"; mkdir -p "$OUT"
cd "$CORPUS" || exit 1
n=0
for f in $(find tests -name '*.k' ! -name '*_member.k' | grep -Eiv 'err|error' | sort); do
    case "$f" in
        # Not scoreable by output, each for its own reason: two run forever and are killed by the
        # timeout, so their length depends on machine load; one prints the path it was invoked
        # with; one reads a freed slot, whose contents are a heap address; and one races three
        # threads on a counter, which is the point of it.
        tests/control-flow/loop.k|tests/control-flow/control_flow.k|tests/functions/main_args.k) continue ;;
        tests/stdlib-heap/heap_basic.k|tests/stdlib-threads/thread_shared.k) continue ;;
    esac
    key=$(echo "$f" | tr '/' '_')
    if ! "$C" "$f" -o "$T/o.s" >/dev/null 2>&1; then echo "BUILDFAIL" > "$OUT/$key"; n=$((n+1)); continue; fi
    if ! nasm -O1 -felf64 "$T/o.s" -o "$T/o.o" 2>/dev/null || ! ld "$T/o.o" "$CORPUS/print.o" -o "$T/o.bin" 2>/dev/null; then
        echo "LINKFAIL" > "$OUT/$key"; n=$((n+1)); continue
    fi
    timeout 10 "$T/o.bin" > "$OUT/$key" 2>&1
    echo "EXIT=$?" >> "$OUT/$key"
    n=$((n+1))
done
echo "recorded $n programs into $OUT"
