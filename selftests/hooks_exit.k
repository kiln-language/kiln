// The `exit` builtin runs the `@fini` hooks too, then exits with its status.
pub unsafe builtin syscall nr:long args:...long -> long;
pub builtin exit status:long -> never;
var gSeen: long = 0;
@fini note -> void { gSeen = 1; }
@fini check -> void { if (gSeen != 0) { unsafe { syscall(60, 99); } } }   // runs first: gSeen still 0
leave code:long -> never { exit(code); }
main -> long {
    x: long = 40;
    leave(x + 4);
}
