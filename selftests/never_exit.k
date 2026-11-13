// A call to a `-> never` function as main's last statement: no `return` after it, and the process
// ends with its status.
die code:long -> never { unsafe { asm -> never { in rdi code; "mov rax, 60" "syscall" } } }
main -> long { x: long = 40; die(x + 2); }
