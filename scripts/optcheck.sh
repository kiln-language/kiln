#!/bin/bash
# What the optimizer is supposed to have done, read off the IR it leaves. Each program in
# selftests/opt/ states its own expectations in comments, about one function's optimized IR
# (`--emit=ir`, after inlining and flow.k):
#
#     // ir-lacks: <function> <text>     the function's IR does not contain <text>
#     // ir-has:   <function> <text>     it does
#     // ir-count: <function> <text> <n>  exactly n of its lines contain <text>
#     // ir-before: <function> <text> <label>  the first line with <text> comes before `<label>:`
#     // ir-after:  <function> <text> <label>  every line with <text> comes after `<label>:`
#
# or about what the back end wrote for it, read off the assembly (the function's label to the
# next function's `align`, its out-of-line code included), for what the IR cannot show: the
# frame, the prologue, the registers a value passes through:
#
#     // asm-has:   <function> <text>     the function's assembly contains <text>
#     // asm-lacks: <function> <text>     it does not
#     // asm-count: <function> <text> <n> exactly n of its lines contain <text>
#     // asm-first: <function> <text>     its first instruction contains <text>
#
# and must also build and exit 0. Run from the repository root; pass the compiler as $1.
C=${1:-build/gen1}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
pass=0; fail=0
for f in selftests/opt/*.k; do
    name=$(basename "$f" .k)
    if ! "$C" "$f" --emit=ir > "$T/ir" 2>&1; then echo "  $name: --emit=ir failed"; fail=$((fail+1)); continue; fi
    rm -f "$T/t.s"
    "$C" "$f" -o "$T/t.s" >/dev/null 2>&1
    ok=1
    while IFS= read -r line; do
        akind=$(echo "$line" | sed -n -E 's#^// asm-(has|lacks|count|first):.*#\1#p')
        if [ -n "$akind" ]; then
            fn=$(echo "$line" | sed 's|^// asm-[a-z]*: \([^ ]*\) .*|\1|')
            text=$(echo "$line" | sed 's|^// asm-[a-z]*: [^ ]* ||')
            label="mfn_$(echo "$fn" | sed 's|::|$|g')"
            body=$(awk -v l="$label:" '$0 == l {on=1; next} /^align / {on=0} on' "$T/t.s" 2>/dev/null)
            [ -z "$body" ] && { echo "  $name: no function $fn in the assembly"; ok=0; continue; }
            case $akind in
                count) want=${text##* }; text=${text% *}
                       got=$(echo "$body" | grep -cF -- "$text")
                       [ "$got" != "$want" ] && { echo "  $name: $fn has $got lines of assembly with '$text', wanted $want"; ok=0; } ;;
                first) echo "$body" | head -1 | grep -qF -- "$text" || { echo "  $name: $fn begins '$(echo "$body" | head -1)', not '$text'"; ok=0; } ;;
                has)   echo "$body" | grep -qF -- "$text" || { echo "  $name: $fn's assembly lacks '$text'"; ok=0; } ;;
                lacks) echo "$body" | grep -qF -- "$text" && { echo "  $name: $fn's assembly still has '$text'"; ok=0; } ;;
            esac
            continue
        fi
        # This sed uses `#` as its delimiter. With `|` as the delimiter, the `\|` in the pattern was
        # a literal bar rather than alternation, so no expectation ever matched and only the exit
        # codes were checked.
        kind=$(echo "$line" | sed -n -E 's#^// ir-(has|lacks|count|before|after):.*#\1#p')
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
        if [ "$kind" = before ] || [ "$kind" = after ]; then
            label=${text##* }; text=${text% *}
            tl=$(echo "$body" | grep -nF -- "$text" | head -1 | cut -d: -f1)
            ll=$(echo "$body" | grep -nxF -- "$label:" | head -1 | cut -d: -f1)
            if [ -z "$tl" ] || [ -z "$ll" ]; then echo "  $name: $fn lacks '$text' or '$label:'"; ok=0; continue; fi
            if [ "$kind" = before ] && [ "$tl" -gt "$ll" ]; then echo "  $name: $fn has '$text' only after '$label:'"; ok=0; fi
            if [ "$kind" = after ] && [ "$tl" -lt "$ll" ]; then echo "  $name: $fn has '$text' before '$label:'"; ok=0; fi
            continue
        fi
        if echo "$body" | grep -qF -- "$text"; then has=1; else has=0; fi
        if [ "$kind" = has ] && [ $has = 0 ]; then echo "  $name: $fn lacks '$text'"; ok=0; fi
        if [ "$kind" = lacks ] && [ $has = 1 ]; then echo "  $name: $fn still has '$text'"; ok=0; fi
    done < "$f"
    if [ -f "$T/t.s" ] && nasm -O1 -felf64 "$T/t.s" -o "$T/t.o" && ld "$T/t.o" -o "$T/t.bin"; then
        # A probe that never ends fails rather than holding the run (124, `timeout`'s status).
        timeout 20 "$T/t.bin" > /dev/null 2>&1; rc=$?
        [ $rc -ne 0 ] && { echo "  $name: exit $rc, wanted 0"; ok=0; }
    else echo "  $name: build failed"; ok=0; fi
    if [ $ok = 1 ]; then pass=$((pass+1)); else fail=$((fail+1)); fi
done
echo "optcheck     pass=$pass fail=$fail"
[ $fail -eq 0 ]
