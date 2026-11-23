// A branch past one instruction that only changes a value is written without the branch: `set<cc>`
// and an add for `n += 1` (or `-= 1`), a conditional move for a copy, a constant, a sum or a
// difference. Every comparison and signedness, a narrow value that wraps, the comparison fused
// with a load or a mask, operands in slots, and a label another branch also names.

countGt xs:[long] lim:long -> long { n: long = 0; for i in 0..xs.len { if (xs[i] > lim) { n += 1; } } return n; }
countLeU xs:[u32] lim:u32 -> long { n: long = 0; for i in 0..xs.len { if (xs[i] <= lim) { n += 1; } } return n; }
countEq xs:[int] v:int -> long { n: long = 0; for i in 0..xs.len { if (xs[i] == v) { n -= 1; } } return n; }
odd xs:[long] -> long { n: long = 0; for i in 0..xs.len { if ((xs[i] & 1) != 0) { n += 1; } } return n; }
// A narrow counter that wraps at its width.
wrapCount xs:[long] -> u8 { n: u8 = 250; for i in 0..xs.len { if (xs[i] >= 0) { n += 1; } } return n; }
// A copy, a constant, a sum with a register, a difference.
maxOf xs:[long] -> long { m: long = xs[0]; for i in 0..xs.len { if (xs[i] > m) { m = xs[i]; } } return m; }
clampLow x:long -> long { r: long = x; if (r < -5) { r = -5; } return r; }
bump x:long y:long -> long { r: long = x; if (y >= 3) { r = x + y; } return r * 10 + y; }
lower x:long -> long { r: long = x; if (x <= 0) { r = x - 7; } return r; }
wide x:long -> long { r: long = x; if (x != 4) { r = x + 2147483647; } return r; }
// An unsigned comparison and a narrow signed value.
uMin x:u64 y:u64 -> u64 { r: u64 = x; if (y < x) { r = y; } return r; }
sMin x:i16 y:i16 -> i16 { r: i16 = x; if (y < x) { r = y; } return r; }
// A label another branch also names: the move must not disturb the other way in.
twoWays x:long y:long -> long {
    r: long = 0;
    if (x > 10) { r = 100; } else { r = 1; if (y > 0) { r = 2; } }
    return r;
}
// Many values live, so the moved value comes from a slot.
crowd xs:[long] -> long {
    a: long = xs[0] * 3; b: long = xs[1] * 5; c: long = xs[2] * 7; d: long = xs[3] * 11;
    e: long = a + b; f: long = c + d; g: long = a - d; h: long = b - c;
    r: long = 0;
    for i in 0..xs.len { if (xs[i] > 2) { r = e; } if (xs[i] < 0) { r = g; } }
    return r + a + b + c + d + e + f + g + h;
}

main -> int {
    cg: fn([long], long) -> long = &countGt;
    cu: fn([u32], u32) -> long = &countLeU;
    ce: fn([int], int) -> long = &countEq;
    od: fn([long]) -> long = &odd;
    wc: fn([long]) -> u8 = &wrapCount;
    xs: [long; 8] = [5, -3, 0, 12, -7, 9, 2, 3];
    if (cg(xs[..], 2) != 4 || cg(xs[..], 100) != 0 || od(xs[..]) != 5) { return 1; }
    us: [u32; 4] = [0, 4294967295, 7, 2147483648];
    if (cu(us[..], 7) != 2 || cu(us[..], 2147483648) != 3) { return 2; }
    is: [int; 5] = [-1, 3, -1, -1, 0];
    if (ce(is[..], -1) != -3) { return 3; }
    if (wc(xs[..]) != 0 as u8) { return 4; }
    mx: fn([long]) -> long = &maxOf;
    cl: fn(long) -> long = &clampLow;
    bp: fn(long, long) -> long = &bump;
    lw: fn(long) -> long = &lower;
    wd: fn(long) -> long = &wide;
    if (mx(xs[..]) != 12 || cl(-9) != -5 || cl(-2) != -2) { return 5; }
    if (bp(10, 3) != 133 || bp(10, 2) != 102 || lw(0) != -7 || lw(1) != 1) { return 6; }
    if (wd(4) != 4 || wd(5) != 2147483652) { return 7; }
    um: fn(u64, u64) -> u64 = &uMin;
    sm: fn(i16, i16) -> i16 = &sMin;
    big: u64 = ~(0 as u64);
    if (um(big, 3 as u64) != 3 as u64 || um(3 as u64, big) != 3 as u64) { return 8; }
    if (sm(-3 as i16, 2 as i16) != -3 as i16 || sm(5 as i16, -32768 as i16) != -32768 as i16) { return 9; }
    tw: fn(long, long) -> long = &twoWays;
    if (tw(11, 5) != 100 || tw(1, 5) != 2 || tw(1, -5) != 1) { return 10; }
    cr: fn([long]) -> long = &crowd;
    if (cr(xs[..]) != 132) { return 11; }
    return 0;
}
