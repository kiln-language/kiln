// `@init` hooks run before main, in declaration order, dependencies first; `@fini` after it, in
// reverse. This one's last hook exits with what the others recorded, so the exit status says
// all three ran, and in which order.
pub unsafe builtin syscall nr:long args:...long -> long;
var gLog: long = 0;
@init first -> void { gLog = gLog * 10 + 1; }
@init second -> void { gLog = gLog * 10 + 2; }
@fini closeA -> void { unsafe { syscall(60, gLog); } }       // runs last: 12 * 10 + 3 = 123
@fini closeB -> void { gLog = gLog * 10 + 3; }               // runs first
main -> long {
    if (gLog != 12) { return 1; }
    return 0;
}
