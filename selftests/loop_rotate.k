// Loops whose jump back is written as their test turned round: every kind of test (signed and
// unsigned, narrow widths that wrap, a bool), `continue` (a second way back to the test), `break`,
// nesting, a last block where an `if`'s arms meet (left as it was), a bound the body changes, and
// a loop that never runs. Through fn values, so nothing folds the bounds.
signedDown n:long -> long { s: long = 0; i: long = n; while (i > -3) { s += i; i -= 1; } return s; }
unsignedUp n:u32 -> long { s: long = 0; i: u32 = 4294967290; while (i >= 4294967290) { s += 1; i += n; } return s; }
narrowWrap start:u8 -> long { s: long = 0; i: u8 = start; while (i != 3) { s += 1; i += 1; } return s; }
i16Down start:i16 -> long { s: long = 0; i: i16 = start; while (i > -32760) { s += 1; i -= 3; } return s; }
flagLoop n:long -> long { s: long = 0; go: bool = n > 0; while (go) { s += 1; go = s < n; } return s; }
withContinue n:long -> long {
    s: long = 0;
    i: long = 0;
    while (i < n) {
        i += 1;
        if (i % 3 == 0) { continue; }
        s += i;
    }
    return s;
}
withBreak n:long -> long { s: long = 0; for i in 0..n { if (i == 7) { break; } s += i; } return s; }
nested n:long -> long { s: long = 0; for i in 0..n { for j in i..n { s += j - i; } } return s; }
merges n:long -> long {
    s: long = 0;
    i: long = 0;
    while (i < n) {
        if (i % 2 == 0) { s += 1; } else { s += 10; }
        i += 1;
    }
    return s;
}
moving xs:[long] -> long { n: long = xs.len; k: long = 0; while (k < n) { if (xs[k] < 0) { n = k; } k += 1; } return n; }
never n:long -> long { s: long = 0; for i in n..0 { s += 1; } return s; }

main -> int {
    a: fn(long) -> long = &signedDown;
    b: fn(u32) -> long = &unsignedUp;
    c: fn(u8) -> long = &narrowWrap;
    d: fn(i16) -> long = &i16Down;
    e: fn(long) -> long = &flagLoop;
    if (a(3) != 3 + 2 + 1 + 0 - 1 - 2) { return 1; }
    if (b(1) != 6 || b(3) != 2) { return 2; }
    if (c(250) != 9 || c(3) != 0) { return 3; }
    if (d(-32740) != 7) { return 4; }
    if (e(5) != 5 || e(0) != 0) { return 5; }
    if (withContinue(10) != 1 + 2 + 4 + 5 + 7 + 8 + 10) { return 6; }
    if (withBreak(100) != 21 || withBreak(3) != 3) { return 7; }
    if (nested(4) != 10) { return 8; }
    if (merges(5) != 23) { return 9; }
    xs: [long; 5] = [1, 2, -1, 4, 5];
    if (moving(xs[..]) != 2) { return 10; }
    if (never(5) != 0) { return 11; }
    return 0;
}
