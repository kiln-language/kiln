// A call's result that an instruction a few places on reads is read just after the call, from
// `rax` (`Opt.pullResults`), but only past instructions that neither write what that reader reads
// nor read what it writes. The first loop's reader moves; the other two may not.
spin n:long -> long {
    s: long = 0;
    for i in 0..n { s += i * 3 + 1; }
    return s;
}
main -> int {
    w: long = 0;
    t1: long = 0;
    for k in 0..10 {
        r: long = spin(k);
        w = w + k;
        t1 = t1 + r;            // reads only the result and t1: moves up
    }
    x: long = 5;
    t2: long = 0;
    for k in 0..10 {
        r: long = spin(k);
        x = x + k;
        t2 = t2 + (r ^ x);      // x was written in between: stays
    }
    b: long = 7;
    t3: long = 0;
    for k in 0..10 {
        r: long = spin(k + 3);
        a: long = b * 3;
        b = r + 2;              // b was read in between: stays
        t3 = t3 + a;
    }
    if (t1 != 405 || w != 45 || spin(4) != 22) { return 1; }
    return (t2 % 100 + t3 % 100) as int;
}
