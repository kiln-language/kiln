// An `asm` block's `out` names something declared: a local, a parameter or a global.
main -> int {
    unsafe { asm { in rax 7; out zz rax; } }
    return 0;
}
