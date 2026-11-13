// stdlib::process: start programs, wait for them, and read how they ended. Exits 0 when every
// check holds, otherwise the number of the first one that did not.
#include <stdlib::process>
#include <stdlib::option>
#include <stdlib::result>
#include <stdlib::string>
#include <stdlib::vec>

codeOf r:Result<ExitStatus, long> -> long {
    match r {
        Ok(s) {
            match s {
                Exited(c)   { return c; }
                Signaled(n) { return 1000 + n; }
            }
        }
        Err(e) { return -e; }
    }
}

// The accessors agree with the variants.
accessorsAgree -> bool {
    a: ExitStatus = ExitStatus.Exited(3);
    b: ExitStatus = ExitStatus.Signaled(9);
    return !a.success() && a.exited() && a.code().unwrapOr(-1) == 3 && a.signal().isNone()
        && !b.exited() && b.signal().unwrapOr(-1) == 9 && b.code().isNone();
}

none -> Vec<str> { v: Vec<str> = vec![]; return v; }

main -> int {
    // PATH lookup, and the exit code coming back.
    if (codeOf(runProcess("sh", vec!["-c", "exit 7"])) != 7) { return 1; }
    if (codeOf(runProcess("true", none())) != 0) { return 2; }
    // Arguments arrive in order, argv[0] being the program as named.
    if (codeOf(runProcess("sh", vec!["-c", "test \"$1$2\" = ab", "sh", "a", "b"])) != 0) { return 3; }
    // A program nothing on PATH names is ENOENT from the spawn, not a child exiting 127.
    if (codeOf(runProcess("no-such-program-kiln-selftest", none())) != -2) { return 4; }
    // A path that is not runnable reports execve's own errno (EACCES).
    if (codeOf(runProcess("/proc/self/environ", none())) != -13) { return 5; }
    // A signal is told apart from an exit code.
    if (codeOf(runProcess("sh", vec!["-c", "kill -9 $$"])) != 1009) { return 6; }
    // Two at once, reaped in whichever order they finish.
    a: Result<Child, long> = spawnProcess("sh", vec!["-c", "exit 11"]);
    b: Result<Child, long> = spawnProcess("sh", vec!["-c", "exit 12"]);
    if (a.isErr() || b.isErr()) { return 7; }
    sum: long = 0;
    n: long = 0;
    while (n < 2) {
        g: Result<(long, ExitStatus), long> = waitAnyProcess();
        match g { Ok(x) { pid, st = x; sum = sum + st.code().unwrapOr(0); } Err(_) { return 8; } }
        n = n + 1;
    }
    if (sum != 23) { return 9; }
    // The environment is there to be read.
    p: Option<str> = envVar("PATH");
    if (p.isNone()) { return 10; }
    if (!accessorsAgree()) { return 11; }
    // A child given its own environment sees that and nothing else.
    e: Result<Child, long> = spawnProcessEnv("sh", vec!["-c", "test \"$KILN_T\" = yes && test -z \"$HOME\""], vec!["KILN_T=yes"]);
    match e {
        Ok(c) { if (codeOf(c.wait()) != 0) { return 12; } }
        Err(_) { return 13; }
    }
    return 0;
}
