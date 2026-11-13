#!/bin/bash
# Differential check for the LLVM back end: compile each program down BOTH paths and compare
# The native path is the oracle. Programs are bare scalar ones, so no runtime is dragged in and
# clang can link the LLVM side as an ordinary C main.
cd "$(dirname "$0")/.."
# Built here: WSL clears /tmp between invocations, so the compiler cannot be handed in.
./bootstrap/kilnc main.k -o /tmp/lvc.s > /dev/null
nasm -O1 -felf64 /tmp/lvc.s -o /tmp/lvc.o
ld /tmp/lvc.o -o /tmp/lvc
C=/tmp/lvc
# A short path: a Kiln diagnostic leads with the file name and a long one crowds out the message.
D=/tmp/lc; rm -rf "$D"; mkdir -p "$D"

pass=0; fail=0
check () {   # check <name> <source>
    local name=$1 src=$2
    printf '%s' "$src" > "$D/p.k"

    # native
    if ! "$C" "$D/p.k" -o "$D/p.s" > "$D/err" 2>&1; then
        printf "  %-22s native REFUSED: %s\n" "$name" "$(sed "s|.*/p.k:|p.k:|" "$D/err" | head -c 80)"; fail=$((fail+1)); return
    fi
    nasm -O1 -felf64 "$D/p.s" -o "$D/p.o" 2>/dev/null && ld "$D/p.o" -o "$D/native" 2>/dev/null
    "$D/native"; local nrc=$?

    # llvm
    if ! "$C" "$D/p.k" --emit=llvm -o /dev/null > "$D/p.ll" 2>"$D/lerr"; then
        printf "  %-22s llvm refused: %s\n" "$name" "$(head -c 70 "$D/p.ll" "$D/lerr" | tr -d '\n' | head -c 70)"
        fail=$((fail+1)); return
    fi
    if ! llvm-as "$D/p.ll" -o "$D/p.bc" 2>"$D/aerr"; then
        printf "  %-22s INVALID IR: %s\n" "$name" "$(head -c 90 "$D/aerr")"; fail=$((fail+1)); return
    fi
    if ! clang -O2 -w -nostdlib -static -no-pie "$D/p.ll" -o "$D/llvm" 2>"$D/cerr"; then
        printf "  %-22s clang failed: %s\n" "$name" "$(head -c 90 "$D/cerr")"; fail=$((fail+1)); return
    fi
    "$D/llvm"; local lrc=$?

    if [ "$nrc" = "$lrc" ]; then
        printf "  %-22s native=%-4s llvm=%-4s  agree\n" "$name" "$nrc" "$lrc"; pass=$((pass+1))
    else
        printf "  %-22s native=%-4s llvm=%-4s  DISAGREE\n" "$name" "$nrc" "$lrc"; fail=$((fail+1))
    fi
}

check arithmetic   'main -> int { return 2 + 3 * 4 - 1; }'
check precedence   'main -> int { return (10 - 4) * 7 % 100; }'
check locals       'main -> int { a: long = 6; b: long = 7; c: long = a * b; return c as int; }'
check while_loop   'main -> int { i: long = 0; n: long = 0; while (i < 10) { n = n + i; i = i + 1; } return n as int; }'
check if_else      'main -> int { x: long = 7; if (x > 5) { return 42; } return 1; }'
check nested_if    'main -> int { n: long = 0; i: long = 0; while (i < 20) { if (i % 3 == 0) { n = n + 1; } i = i + 1; } return n as int; }'
check call         'add a:long b:long -> long { return a + b; }
main -> int { return add(20, 22) as int; }'
check call_chain   'sq x:long -> long { return x * x; }
dbl x:long -> long { return x + x; }
main -> int { return dbl(sq(4)) as int; }'
check recursion    'fib n:long -> long { if (n < 2) { return n; } return fib(n - 1) + fib(n - 2); }
main -> int { return fib(10) as int; }'
check bitwise      'main -> int { a: long = 12; b: long = 10; return ((a & b) + (a | b) + (a ^ b)) as int; }'
check shifts       'main -> int { a: long = 3; return ((a << 4) + (a >> 1)) as int; }'
check comparisons  'main -> int { a: long = 5; b: long = 9; n: long = 0;
    if (a < b) { n = n + 1; } if (a <= b) { n = n + 2; } if (b > a) { n = n + 4; }
    if (b >= a) { n = n + 8; } if (a != b) { n = n + 16; } if (a == a) { n = n + 32; } return n as int; }'
check narrow_cast  'main -> int { x: long = 300; y: u8 = x as u8; return y as int; }'
check signed_cast  'main -> int { x: long = 0 - 56; y: u8 = x as u8; return y as int; }'
check bnot         'main -> int { a: long = 5; b: long = ~a; return (b + 261) as int; }'

check struct_field    'struct P { x: long, y: long }
main -> int { p: P = P { x: 30, y: 12 }; return (p.x + p.y) as int; }'
check struct_assign   'struct P { x: long, y: long }
main -> int { a: P = P { x: 7, y: 5 }; b: P = a; b.x = b.x + 1; return (a.x + b.x + b.y) as int; }'
check struct_arg      'struct P { x: long, y: long }
sum p:P -> long { return p.x + p.y; }
main -> int { return sum(P { x: 20, y: 22 }) as int; }'
check struct_return   'struct P { x: long, y: long }
mk a:long b:long -> P { return P { x: a, y: b }; }
main -> int { p: P = mk(19, 23); return (p.x + p.y) as int; }'
check nested_struct   'struct Inner { v: long }
struct Outer { i: Inner, n: long }
main -> int { o: Outer = Outer { i: Inner { v: 10 }, n: 32 }; return (o.i.v + o.n) as int; }'
check local_array     'main -> int { a: [long; 8]; i: long = 0; while (i < 8) { a[i] = i * i; i = i + 1; }
    return (a[3] + a[5] + a[7]) as int; }'
check array_narrow    'main -> int { a: [u8; 4]; a[0] = 200; a[1] = 55; a[2] = 0; a[3] = 1;
    return (a[0] + a[1] + a[3]) as int; }'
check ptr_write       'main -> int { x: long = 5; p: long = 0;
    unsafe { p = &x; } unsafe { q: *long = p as *long; q[0] = 37; } return x as int; }'
check fnptr           'twice n:long -> long { return n * 2; }
main -> int { f: fn(long)->long = &twice; return f(21) as int; }'

# Floats: arithmetic, NaN comparisons, the conversions, f32, and floats as arguments and results.
check float_arith     'add a:f64 b:f64 -> f64 { return a + b; }
main -> int { x: f64 = add(0.1, 0.2); if (x != 0.30000000000000004) { return 1; } return (add(2.5, 39.75) as long) as int; }'
check float_nan       'div a:f64 b:f64 -> f64 { return a / b; }
main -> int { n: f64 = div(0.0, 0.0); r: int = 0; if (n == n) { r = r | 1; } if (n != n) { r = r | 2; }
    if (n < 1.0) { r = r | 4; } if (!(n >= 1.0)) { r = r | 8; } return r; }'
check float_convert   'f a:long -> f64 { return a as f64; }
g x:f64 -> long { return x as long; }
main -> int { return (g(f(7) * 2.75) + g(0.0 - 2.9) + ((f(5) as f32) as f64 as long)) as int; }'
check float_f32       'm a:f32 b:f32 -> f32 { return a * b - 0.5; }
main -> int { return (m(2.5, 3.0) as long) as int; }'
check float_args      'mix a:long x:f64 b:long y:f32 c:f64 -> f64 { return (a as f64) * x + (b as f64) + (y as f64) * c; }
main -> int { return (mix(2, 1.5, 3, 0.5, 4.0) * 4.0) as long as int; }'

# `asm`: a real syscall, which is what every program reaches through the standard library.
check syscall_exit    '#include <stdlib::sys>
main -> int { sysExit(42); return 7; }'

echo
echo "  agree: $pass   problems: $fail"
