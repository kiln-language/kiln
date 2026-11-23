; The foreign half of xmm_foreign.k: `clobber x:f64 -> f64` returns x + 1 (in xmm0, its bits in
; rax, as a Kiln function returns a float) after writing garbage over xmm1-xmm15, which System V
; allows any function to do.
section .text
global mfn_xmm_foreign$clobber
mfn_xmm_foreign$clobber:
    mov rax, 0x7ff8dead0000beef
    movq xmm1, rax
    movaps xmm2, xmm1
    movaps xmm3, xmm1
    movaps xmm4, xmm1
    movaps xmm5, xmm1
    movaps xmm6, xmm1
    movaps xmm7, xmm1
    movaps xmm8, xmm1
    movaps xmm9, xmm1
    movaps xmm10, xmm1
    movaps xmm11, xmm1
    movaps xmm12, xmm1
    movaps xmm13, xmm1
    movaps xmm14, xmm1
    movaps xmm15, xmm1
    mov rax, 0x3ff0000000000000      ; 1.0
    movq xmm1, rax
    addsd xmm0, xmm1
    movq rax, xmm0
    ret

; `entryAlign -> long`: rsp modulo 16 as this function starts. A caller that keeps the stack the
; way System V requires (16-aligned at the `call`) leaves it at 8, the return address having been
; pushed since.
global mfn_xmm_foreign$entryAlign
mfn_xmm_foreign$entryAlign:
    mov rax, rsp
    and rax, 15
    ret

; `gclobber x:long -> long`: x + 1, after writing garbage over every general register System V
; lets a callee change (rax, rcx, rdx, rsi, rdi, r8 to r11), as a C function may.
global mfn_xmm_foreign$gclobber
mfn_xmm_foreign$gclobber:
    lea r11, [rax + 1]
    mov rax, 0x5a5a5a5a5a5a5a5a
    mov rcx, rax
    mov rdx, rax
    mov rsi, rax
    mov rdi, rax
    mov r8, rax
    mov r9, rax
    mov r10, rax
    mov rax, r11
    mov r11, rcx
    ret
