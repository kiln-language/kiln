#!/bin/bash
# What the optimizer is supposed to have done, read off the IR it leaves. Each program in
# selftests/opt/ states its own expectations in comments, about one function's optimized IR
# (`--emit=ir`, after inlining and flow.k):
#
#     // ir-lacks: <function> <text>     the function's IR does not contain <text>
#     // ir-has:   <function> <text>     it does
#     // ir-count: <function> <text> <n>  exactly n of its lines contain <text>
#
# and must also build and exit 0. Run from the repository root; pass the compiler as $1.
C=${1:-build/gen1}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
pass=0; fail=0
for f in selftests/opt/*.k; do
    name=$(basename "$f" .k)
    if ! "$C" "$f" --emit=ir > "$T/ir" 2>&1; then echo "  $name: --emit=ir failed"; fail=$((fail+1)); continue; fi
    ok=1
    while IFS= read -r line; do
        kind=$(echo "$line" | sed -n 's|^// ir-\(has\|lacks\|count\):.*|\1|p')
        [ -z "$kind" ] && continue
        fn=$(echo "$line" | sed 's|^// ir-[a-z]*: \([^ ]*\) .*|\1|')
        text=$(echo "$line" | sed 's|^// ir-[a-z]*: [^ ]* ||')
        body=$(awk -v fn="fn $fn" '$0 == fn {on=1; next} /^fn / {on=0} on' "$T/ir")
        [ -z "$body" ] && { echo "  $name: no function $fn in the IR"; ok=0; continue; }
        if [ "$kind" = count ]; then
            want=${text##* }; text=${text% *}
            got=$(echo "$body" | grep -cF -- "$text")
            [ "$got" != "$want" ] && { echo "  $name: $fn has $got lines with '$text', wanted $want"; ok=0; }
            continue
        fi
        if echo "$body" | grep -qF -- "$text"; then has=1; else has=0; fi
        if [ "$kind" = has ] && [ $has = 0 ]; then echo "  $name: $fn lacks '$text'"; ok=0; fi
        if [ "$kind" = lacks ] && [ $has = 1 ]; then echo "  $name: $fn still has '$text'"; ok=0; fi
    done < "$f"
    if "$C" "$f" -o "$T/t.s" >/dev/null 2>&1 && nasm -O1 -felf64 "$T/t.s" -o "$T/t.o" && ld "$T/t.o" -o "$T/t.bin"; then
        "$T/t.bin" > /dev/null 2>&1; rc=$?
        [ $rc -ne 0 ] && { echo "  $name: exit $rc, wanted 0"; ok=0; }
    else echo "  $name: build failed"; ok=0; fi
    if [ $ok = 1 ]; then pass=$((pass+1)); else fail=$((fail+1)); fi
done
echo "optcheck     pass=$pass fail=$fail"
[ $fail -eq 0 ]
