#!/bin/bash
# What a call to each function may change, as the compiler worked it out from the text it wrote
# (`--trace-ipra`, relax.k), held to that text read again by scripts/ipracheck.py, which has an
# instruction table of its own: every register a function's lines name or write without naming
# must be in its set. Run over the compiler compiling itself, every selftest it compiles, and the
# corpus. Run from the repository root and pass the compiler (default build/gen1).
C=${1:-build/gen1}
C=$(cd "$(dirname "$C")" && pwd)/$(basename "$C")
ROOT=$(pwd)
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
n=0; fail=0
check() {
    "$C" "$1" -o "$T/a.s" --trace-ipra 2> "$T/trace" > /dev/null || return 0   # a refused program has nothing to check
    n=$((n+1))
    if ! python3 -I "$ROOT/scripts/ipracheck.py" "$T/a.s" "$T/trace" > "$T/r" 2>&1; then
        fail=$((fail+1))
        echo "  $1: $(head -1 "$T/r")"
    fi
}
check main.k
for f in selftests/*.k selftests/opt/*.k; do check "$f"; done
cd "$ROOT/../Kiln" || exit 1
for f in $(find tests -name '*.k' ! -name '*_member.k' | grep -Eiv 'err|error' | sort); do check "$f"; done
echo "ipracheck    checked=$n fail=$fail"
[ $fail = 0 ]
