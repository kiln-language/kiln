// Registers chosen for what a value meets (`RegAlloc.hint`): a parameter kept where its argument
// arrives, a call's argument computed where it leaves from, a shift's count kept in `rcx` and
// shifted by `cl` where it lands (`emitShift`), a returned constant or comparison made straight
// in `rax`. Each answer is what the program gives built without them (`--no-hints`,
// `--no-result-rax`).

var gSink: long = 0;
var gSpin: long = 0;

// Each function below holds a loop, so it stays a call and its parameters arrive as arguments.

// Every parameter arrives in its own register; `c` arrives in `rcx` and is read after the
// shift by `s`, which wants `rcx` too.
local spread a:long b:long c:long d:long e:long f:long s:long -> long {
    for i in 0..(f & 1) + 1 { gSpin = gSpin ^ i; }
    x: long = (a << s) + c;
    y: long = (b >> s) ^ d;
    return x * 3 + y * 5 + e * 7 + f + c;
}

// A narrow shift: the result wraps at 32 bits and is read back signed.
local narrow v:int n:long -> long {
    for i in 0..(n & 1) + 1 { gSpin = gSpin ^ i; }
    r: int = v << n;
    return r as long;
}

// Unsigned and signed shifts right by a count used again afterwards.
local logical v:u64 n:long -> long {
    for i in 0..(n & 1) + 1 { gSpin = gSpin ^ i; }
    r: u64 = v >> n;
    return (r as long) + n;
}
local arith v:long n:long -> long {
    for i in 0..(n & 1) + 1 { gSpin = gSpin ^ i; }
    r: long = v >> n;
    return r + n;
}

// The value shifted is its own count.
local selfShift v:long -> long {
    for i in 0..(v & 1) + 1 { gSpin = gSpin ^ i; }
    return v << (v & 7);
}

// A count computed in a loop, and a value that stays live across it.
local bits n:long -> long {
    acc: long = 0;
    keep: long = n * 3;
    for i in 0..n {
        acc = acc | (1 << ((i * 5) & 63));
        acc = acc ^ (keep >> (i & 15));
    }
    return acc + keep;
}

// A parameter live across calls, which change the registers arguments leave in.
local noisy a:long b:long -> long {
    for i in 0..(b & 1) + 1 { gSpin = gSpin ^ i; }
    gSink = gSink + a;
    return a * 2 + b;
}
local across a:long b:long c:long -> long {
    for i in 0..(a & 1) + 1 { gSpin = gSpin ^ i; }
    s: long = noisy(c, b);
    t: long = noisy(b, a);
    u: long = noisy(a, c);
    return s + t * 3 + u * 7 + a + b + c;
}

// Returns: constants, comparisons signed and unsigned, from several places.
local classify x:long -> long {
    for i in 0..(x & 1) + 1 { gSpin = gSpin ^ i; }
    if (x < 0) { return -1; }
    if (x == 0) { return 0; }
    if (x > 1000) { return 2; }
    return 1;
}
local below a:u64 b:u64 -> bool {
    for i in 0..((b & 1) as long) + 1 { gSpin = gSpin ^ i; }
    return a < b;
}
local less a:long b:long -> bool {
    for i in 0..(b & 1) + 1 { gSpin = gSpin ^ i; }
    return a < b;
}
local same a:long b:long -> bool {
    for i in 0..(b & 1) + 1 { gSpin = gSpin ^ i; }
    return a == b;
}
local half -> double {
    for i in 0..(gSpin & 1) + 1 { gSink = gSink + 0; }
    return 0.5;
}

local fless a:double b:double -> bool {
    for i in 0..((a > 0.0) as long) + 1 { gSpin = gSpin ^ i; }
    return a < b;
}

// A float in the middle of the parameters: the general ones still count from the first.
local mixed a:long x:double b:long y:double c:long -> long {
    for i in 0..(c & 1) + 1 { gSpin = gSpin ^ i; }
    return a + b * 10 + c * 100 + ((x + y) * 1000.0) as long;
}

main -> int {
    if (spread(1, 256, 3, 4, 5, 6, 2) != 405) { return 1; }
    if (spread(-7, -256, 9, -4, 2, 1, 63) != -9223372036854775742) { return 2; }
    if (narrow(1073741824, 1) != -2147483648) { return 3; }
    if (narrow(3, 31) != -2147483648) { return 4; }
    if (logical(9223372036854775808, 60) != 68) { return 5; }
    if (logical(18446744073709551615, 3) != 2305843009213693954) { return 5; }
    if (arith(-9223372036854775807 - 1, 60) != 52) { return 6; }
    if (arith(-1000, 3) != -122) { return 6; }
    if (selfShift(5) != 160 || selfShift(-1) != -128) { return 7; }
    if (bits(40) != 8330787646191410519) { return 8; }
    if (bits(7) != 1108378701) { return 8; }
    if (across(3, 5, 7) != 164 || gSink != 15) { return 9; }
    if (across(-2, 11, 4) != 92 || gSink != 28) { return 9; }
    if (classify(-5) != -1 || classify(0) != 0 || classify(5000) != 2 || classify(7) != 1) { return 10; }
    if (!below(1, 9223372036854775808) || below(9223372036854775808, 1)) { return 11; }
    if (less(1, -1) || !less(-1, 1) || !same(4, 4) || same(4, 5)) { return 12; }
    if (half() != 0.5) { return 13; }
    if (half() + half() != 1.0) { return 13; }
    if (!fless(0.5, 2.0) || fless(3.0, -1.0)) { return 16; }
    if (mixed(1, 0.25, 2, 0.5, 3) != 1071) { return 14; }
    if (mixed(-4, 1.5, 7, -0.25, 9) != 2216) { return 15; }
    return 0;
}
