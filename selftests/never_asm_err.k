// An asm block that does not say `-> never` may come back.
die code:long -> never { unsafe { asm { in rdi code; "mov rax, 60" "syscall" } } }
main -> long { die(1); }
