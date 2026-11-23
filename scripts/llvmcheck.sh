#!/bin/bash
# A differential check for the LLVM back end: each program is compiled down BOTH paths and the
# exit codes are compared, with the native path as the oracle. The programs are small ones written
# inline (scalars, structs, arrays, pointers, fn values, floats, one `asm` syscall, narrow `asm`
# outputs and ones into globals, the atomics, `memcpy`); none needs the standard library's
# runtime, so clang links each module on its own with `-nostdlib`.
cd "$(dirname "$0")/.."
# The compiler is built here rather than passed in, because WSL clears /tmp between invocations.
./bootstrap/kilnc main.k -o /tmp/lvc.s > /dev/null
nasm -O1 -felf64 /tmp/lvc.s -o /tmp/lvc.o
ld /tmp/lvc.o -o /tmp/lvc
C=/tmp/lvc
# A short directory, because a Kiln diagnostic starts with the file's path and a long one crowds
# out the message.
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


# The atomic builtins: an acquire load, a release and a sequentially consistent store, a swap, a
# compare-and-swap that fails and one that takes, and an add, on eight-byte and four-byte words.
check atomics         'pub unsafe builtin atomicLoad p:*long -> long;
pub unsafe builtin atomicStore p:*long v:long -> void;
pub unsafe builtin atomicStoreSeqCst p:*long v:long -> void;
pub unsafe builtin atomicSwap p:*long v:long -> long;
pub unsafe builtin atomicCas p:*long expected:long desired:long -> long;
pub unsafe builtin atomicAdd p:*long delta:long -> long;
pub unsafe builtin atomicAdd32 p:*int delta:int -> int;
pub unsafe builtin atomicCas32 p:*int expected:int desired:int -> int;
main -> int { c: [long; 2] = [5, 0]; k: [int; 2] = [0 - 3, 9]; r: long = 0;
    unsafe { p: *long = &c[0] as *long; q: *int = &k[0] as *int;
        atomicStore(p, atomicLoad(p) + 1); atomicStoreSeqCst(p, atomicSwap(p, 7) + 2);
        r = atomicCas(p, 1, 50) + atomicCas(p, 8, 9) + atomicAdd(p, 3);
        r = r + atomicAdd32(q, 5) + atomicCas32(q, 2, 4) + k[0] + k[1]; }
    return (r + c[0] + c[1]) as int; }'

# An `asm` output into locals narrower than a word: each gets the register's low bytes as its
# type, extended the way the type says, whatever was above them.
check asm_narrow      'local asI8 x:long -> i8 { r: i8 = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local asU16 x:long -> u16 { r: u16 = 0; unsafe { asm { in rax x; out r rax; } } return r; }
local asI32 x:long -> int { r: int = 0; unsafe { asm { in rax x; out r rax; } } return r; }
main -> int { n: long = 0;
    if (asI8(0x180) == 0 - 128) { n = n + 1; }
    if (asU16(0x1234FFFB) == 65531) { n = n + 10; }
    if (asI32(0x1FFFFFFFF) == 0 - 1) { n = n + 100; }
    return n as int; }'

# An `asm` output into globals, a word and a narrow one, read back after a call and by a later
# block's `in`.
check asm_global      'var gW: long = 0;
var gH: i16 = 0;
local setW x:long -> void { unsafe { asm { in rax x; out gW rax; } } }
local setH x:long -> void { unsafe { asm { in rax x; out gH rax; } } }
local bump -> void { unsafe { asm { in rax gW; "add rax, 1" out gW rax; } } }
main -> int { n: long = 0;
    setW(40); bump(); bump();
    if (gW == 42) { n = n + 1; }
    setH(0x1234FFFB);
    if (gH == 0 - 5) { n = n + 10; }
    return n as int; }'

# The `memcpy` builtin (`llvm.memcpy` on this path): a copy of nothing, of a word, and of a run.
check memcpy          'pub unsafe builtin memcpy dst:long src:long n:long -> void;
main -> int { a: [long; 4] = [1, 2, 3, 4]; b: [long; 4] = [0, 0, 0, 0];
    unsafe { memcpy(&b[0] as long, &a[0] as long, 0); memcpy(&b[0] as long, &a[1] as long, 8);
        memcpy(&b[1] as long, &a[0] as long, 24); }
    return (b[0] * 1000 + b[1] * 100 + b[2] * 10 + b[3]) as int; }'

echo
echo "  agree: $pass   problems: $fail"
