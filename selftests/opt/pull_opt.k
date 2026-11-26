// A call's result added into a sum two instructions on is added just after the call, read from
// `rax` where it arrives (`Opt.pullResults`), not copied out first. Off with `--no-pull-result`.
// asm-lacks: pull_opt::total mov rbx, rax
// asm-has: pull_opt::total add r9, rax
spin n:long -> long {
    s: long = 0;
    for i in 0..n { s += i * 3 + 1; }
    return s;
}
total n:long -> long {
    w: long = 0;
    t: long = 0;
    for k in 0..n {
        r: long = spin(k);
        w = w + k;
        t = t + r;
    }
    return t + w;
}
main -> int {
    if (total(10) != 450 || total(3) != 9 || spin(4) != 22) { return 1; }
    return 0;
}
