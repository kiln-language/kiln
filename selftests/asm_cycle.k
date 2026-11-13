// An `asm` block's inputs are a parallel move: values sitting in each other's target registers
// (here every pair swapped, with `rax` bound as well) arrive where the block asked, and breaking
// a cycle never borrows a register the block binds. Each input is weighted by a distinct prime.
mix a:long b:long c:long d:long e:long f:long -> long {
    r: long = 0;
    n: long = a * 100;
    unsafe {
        asm {
            in rax n; in rdi b; in rsi a; in rdx d; in rcx c; in r8 f; in r9 e;
            "imul rdi, rdi, 2"
            "imul rsi, rsi, 3"
            "imul rdx, rdx, 5"
            "imul rcx, rcx, 7"
            "imul r8, r8, 11"
            "imul r9, r9, 13"
            "add rax, rdi"
            "add rax, rsi"
            "add rax, rdx"
            "add rax, rcx"
            "add rax, r8"
            "add rax, r9"
            out r rax;
        }
    }
    return r;
}
rot3 a:long b:long c:long -> long {
    r: long = 0;
    unsafe {
        asm {
            in rdi c; in rsi a; in rdx b; in rax b;
            "imul rdi, rdi, 100"
            "imul rsi, rsi, 10"
            "imul rax, rax, 1000"
            "add rax, rdi"
            "add rax, rsi"
            "add rax, rdx"
            out r rax;
        }
    }
    return r;
}
main -> int {
    // n=100, b*2=4, a*3=3, d*5=20, c*7=21, f*11=66, e*13=65
    if (mix(1, 2, 3, 4, 5, 6) != 100 + 4 + 3 + 20 + 21 + 66 + 65) { return 1; }
    // rdi=c*100=300, rsi=a*10=10, rdx=b=2, rax=b*1000=2000
    if (rot3(1, 2, 3) != 2312) { return 2; }
    return 0;
}
