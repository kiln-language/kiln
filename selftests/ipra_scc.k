// Calls inside a cycle of functions (`ping` and `pong` call each other, `again` itself) reach a
// function not yet written when its caller is compiled, so they change every register a callee
// need not keep (`calleesFirst`, `siteMask`): what lives across them is in callee-saved registers
// or the frame, and every value comes back right. `leafy` is outside the cycle and leaves most
// registers alone, which the cycle's members may use across calls to it.

var gSink: long = 0;

leafy x:long -> long {
    s: long = x;
    for i in 0..(x & 1) + 1 { s = s + i; }
    return s;
}

ping n:long -> long {
    if (n <= 0) { return 1; }
    a: long = gSink + n * 3 + 1;
    b: long = gSink + n * 5 + 2;
    c: long = gSink + n * 7 + 3;
    d: long = gSink + n * 9 + 4;
    e: long = gSink + n * 11 + 5;
    r: long = pong(n - 1);
    r = r + leafy(a) + b;
    r = r + pong(n - 2) + c * d + e;
    return (r + a + b + c + d + e) & 1048575;
}

pong n:long -> long {
    if (n <= 0) { return 2; }
    p: long = gSink + n * 13 + 6;
    q: long = gSink + n * 17 + 7;
    u: long = gSink + n * 19 + 8;
    v: long = gSink + n * 23 + 9;
    r: long = ping(n - 1) + leafy(p);
    r = r + q * u + v;
    return (r + p + q + u + v) & 1048575;
}

again n:long acc:long -> long {
    if (n <= 0) { return acc; }
    a: long = gSink + n + 1;
    b: long = gSink + n * 2 + 1;
    c: long = gSink + n * 4 + 1;
    d: long = gSink + n * 8 + 1;
    r: long = again(n - 1, acc + leafy(a));
    r = r + again(n - 3, b);
    return (r + a * b + c * d) & 1048575;
}

main -> long {
    gSink = leafy(0);
    if (ping(12) != 432992) { return 1; }
    if (pong(9) != 118806) { return 2; }
    if (again(11, 3) != 47126) { return 3; }
    return 0;
}
