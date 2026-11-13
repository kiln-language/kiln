#!/bin/bash
# Four ways to build the same four kernels: Kiln's own back end, Kiln through LLVM, gcc and rustc.
#
# The kernels are the scalar ones from ../Kiln/benchmarks (sum, fib, collatz, primes). `sieve`,
# `vector`, `records`, `higher` and `strings` are left out because the LLVM path does not do arrays
# or aggregates yet, and a comparison one entrant cannot enter is not one.
#
# The answer comes back as an exit code rather than printed: printing needs the runtime, the
# runtime is built on `asm`, and `asm` is one of the things the LLVM path still refuses. `% 251`
# keeps the result inside an exit code AND keeps the computation live, so no optimizer deletes it.
# Every build's answer is checked to agree before any of them is timed.
cd "$(dirname "$0")/.."
D=/tmp/four; rm -rf $D; mkdir -p $D

./bootstrap/kilnc main.k -o /tmp/kc.s > /dev/null
nasm -O1 -felf64 /tmp/kc.s -o /tmp/kc.o
ld /tmp/kc.o -o /tmp/kc
K=/tmp/kc

# ---- the kernels, four times each ----------------------------------------
cat > $D/sum.k <<'EOF'
main -> int {
    total: long = 0;
    i: long = 0;
    while (i < 300000000) { total = total + (i * i) % 7; i = i + 1; }
    return (total % 251) as int;
}
EOF
cat > $D/sum.c <<'EOF'
int main(void){ long t=0; for(long i=0;i<300000000;i++) t += (i*i)%7; return (int)(t%251); }
EOF
cat > $D/sum.rs <<'EOF'
fn main(){ let mut t:i64=0; let mut i:i64=0; while i<300000000 { t+=(i*i)%7; i+=1; }
  std::process::exit((t%251) as i32); }
EOF

cat > $D/fib.k <<'EOF'
fib n:long -> long { if (n < 2) { return n; } return fib(n - 1) + fib(n - 2); }
main -> int { return (fib(40) % 251) as int; }
EOF
cat > $D/fib.c <<'EOF'
long fib(long n){ return n<2?n:fib(n-1)+fib(n-2); }
int main(void){ return (int)(fib(40)%251); }
EOF
cat > $D/fib.rs <<'EOF'
fn fib(n:i64)->i64{ if n<2 {n} else {fib(n-1)+fib(n-2)} }
fn main(){ std::process::exit((fib(40)%251) as i32); }
EOF

cat > $D/collatz.k <<'EOF'
collatz_steps n:long -> long {
    steps: long = 0;
    while (n != 1) {
        if (n % 2 == 0) { n = n / 2; } else { n = n * 3 + 1; }
        steps = steps + 1;
    }
    return steps;
}
main -> int {
    best: long = 0;
    besti: long = 0;
    i: long = 1;
    while (i < 1000000) {
        s: long = collatz_steps(i);
        if (s > best) { best = s; besti = i; }
        i = i + 1;
    }
    return ((besti + best) % 251) as int;
}
EOF
cat > $D/collatz.c <<'EOF'
long steps(long n){ long s=0; while(n!=1){ n = (n%2==0)? n/2 : n*3+1; s++; } return s; }
int main(void){ long best=0,bi=0; for(long i=1;i<1000000;i++){ long s=steps(i); if(s>best){best=s;bi=i;} }
  return (int)((bi+best)%251); }
EOF
cat > $D/collatz.rs <<'EOF'
fn steps(mut n:i64)->i64{ let mut s=0i64; while n!=1 { n = if n%2==0 {n/2} else {n*3+1}; s+=1; } s }
fn main(){ let mut best=0i64; let mut bi=0i64; let mut i=1i64;
  while i<1000000 { let s=steps(i); if s>best {best=s; bi=i;} i+=1; }
  std::process::exit(((bi+best)%251) as i32); }
EOF

cat > $D/primes.k <<'EOF'
is_prime n:long -> long {
    if (n < 2) { return 0; }
    i: long = 2;
    while (i * i <= n) { if (n % i == 0) { return 0; } i = i + 1; }
    return 1;
}
main -> int {
    count: long = 0;
    n: long = 0;
    while (n < 2000000) { if (is_prime(n) == 1) { count = count + 1; } n = n + 1; }
    return (count % 251) as int;
}
EOF
cat > $D/primes.c <<'EOF'
long is_prime(long n){ if(n<2) return 0; for(long i=2;i*i<=n;i++) if(n%i==0) return 0; return 1; }
int main(void){ long c=0; for(long n=0;n<2000000;n++) if(is_prime(n)==1) c++; return (int)(c%251); }
EOF
cat > $D/primes.rs <<'EOF'
fn is_prime(n:i64)->i64{ if n<2 {return 0;} let mut i=2i64; while i*i<=n { if n%i==0 {return 0;} i+=1; } 1 }
fn main(){ let mut c=0i64; let mut n=0i64; while n<2000000 { if is_prime(n)==1 {c+=1;} n+=1; }
  std::process::exit((c%251) as i32); }
EOF

BENCH="sum fib collatz primes"

echo "=== building ==="
for b in $BENCH; do
    $K $D/$b.k -o $D/$b.s          > /dev/null 2>&1 && nasm -O1 -felf64 $D/$b.s -o $D/$b.o 2>/dev/null && ld $D/$b.o -o $D/$b.kiln 2>/dev/null
    $K $D/$b.k --emit=llvm -o /dev/null > $D/$b.ll 2>$D/$b.llerr && clang -O2 -w $D/$b.ll -o $D/$b.llvm 2>/dev/null
    gcc -O2 -o $D/$b.gcc $D/$b.c 2>/dev/null
    rustc -O -o $D/$b.rust $D/$b.rs 2>/dev/null
    miss=""
    for v in kiln llvm gcc rust; do [ -x "$D/$b.$v" ] || miss="$miss $v"; done
    [ -n "$miss" ] && echo "  $b: MISSING$miss  $(head -c 80 $D/$b.llerr 2>/dev/null)"
done

echo
echo "=== every build must agree before anything is timed ==="
ok=1
for b in $BENCH; do
    line="  $b:"
    ref=""
    for v in kiln llvm gcc rust; do
        [ -x "$D/$b.$v" ] || { line="$line $v=-"; continue; }
        "$D/$b.$v"; rc=$?
        line="$line $v=$rc"
        [ -z "$ref" ] && ref=$rc
        [ "$rc" != "$ref" ] && ok=0 && line="$line(MISMATCH)"
    done
    echo "$line"
done
[ $ok = 1 ] && echo "  all agree" || { echo "  MISMATCH: not timing"; exit 1; }

echo
echo "=== best of 3, interleaved ==="
declare -A best
for round in 1 2 3; do
    for b in $BENCH; do
        for v in kiln llvm gcc rust; do
            [ -x "$D/$b.$v" ] || continue
            s=$( { /usr/bin/time -f "%e" "$D/$b.$v" > /dev/null; } 2>&1 | tail -1 )
            cur=${best[$b.$v]:-999}
            awk -v n="$s" -v c="$cur" 'BEGIN{exit !(n<c)}' && best[$b.$v]=$s
        done
    done
done
printf "  %-9s %9s %9s %9s %9s\n" bench kiln kiln-llvm "gcc -O2" "rustc -O"
for b in $BENCH; do
    printf "  %-9s %9s %9s %9s %9s\n" "$b" "${best[$b.kiln]:--}" "${best[$b.llvm]:--}" "${best[$b.gcc]:--}" "${best[$b.rust]:--}"
done
