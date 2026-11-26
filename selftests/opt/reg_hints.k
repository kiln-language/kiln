// A register chosen for what its value meets (`RegAlloc.hint`): a shift's count kept in `rcx`
// is shifted by with nothing saved around it (`emitShift`); parameters that arrive in `rbx` and
// `rcx` stay there, rather than each moving one register along; a returned constant or
// comparison is made in `rax` (`markArgOnly`, `markRaxPairs`).
// asm-lacks: reg_hints::gather push rcx
// asm-has: reg_hints::gather , cl
// asm-lacks: reg_hints::scatter push rcx
// asm-lacks: reg_hints::pick mov rcx, rbx
// asm-lacks: reg_hints::pick mov rdi, rcx
// asm-lacks: reg_hints::sign mov rax, r
// asm-lacks: reg_hints::lower mov rax, r

var gSpin: long = 0;

gather v:[u8] n:long -> long {
    acc: long = 0;
    for i in 0..n { acc = acc | ((v[i] as long) << (i * 8)); }
    return acc;
}
// `k` arrives in `rcx` and keeps it, but `step`, which takes over its register where `k` dies,
// would hold `rcx` through the loop the shift wants it in.
scatter v:[u8] n:long k:long -> long {
    step: long = k * 9;
    acc: long = 0;
    for i in 0..n { acc = acc ^ ((v[i] as long) << ((i * step) & 63)); }
    return acc;
}
pick a:long b:long c:long -> long {
    for i in 0..(c & 1) + 1 { gSpin = gSpin ^ i; }
    return b * c + a;
}
sign x:long -> long {
    for i in 0..(x & 1) + 1 { gSpin = gSpin ^ i; }
    if (x < 0) { return -1; }
    if (x > 0) { return 1; }
    return 0;
}
lower a:long b:long -> bool {
    for i in 0..(b & 1) + 1 { gSpin = gSpin ^ i; }
    return a < b;
}
main -> int {
    bytes: [u8; 4] = [1, 2, 3, 4];
    if (gather(bytes[..], 4) != 67305985 || gather(bytes[..], 2) != 513) { return 1; }
    if (scatter(bytes[..], 4, 1) != 537658369 || scatter(bytes[..], 3, 2) != 206158954497) { return 5; }
    if (pick(1, 2, 3) != 7 || pick(5, -1, 4) != 1) { return 2; }
    if (sign(-4) != -1 || sign(0) != 0 || sign(9) != 1) { return 3; }
    if (!lower(1, 2) || lower(2, 1)) { return 4; }
    return 0;
}
