// Running other programs: start one, wait for it, read how it ended.
//
//     st: Result<ExitStatus, long> = runProcess("nasm", vec!["-felf64", "a.s", "-o", "a.o"]);
//     match st {
//         Ok(s)  { if (!s.success()) { eprintln("nasm {}", s.describe()); } }
//         Err(e) { eprintln("could not start nasm (errno {})", e); }
//     }
//
// A program named without a `/` is looked up on PATH, the way a shell would; one with a `/` is
// taken as written. The child inherits this process's standard streams and working directory,
// and its environment unless `spawnProcessEnv` is handed one.
//
// A child is started with `clone(CLONE_VM | CLONE_VFORK)` followed directly by `execve`, as
// `posix_spawn` does. For the few instructions between the two calls the child shares this
// process's memory instead of copying its page tables, so the cost does not grow with the size
// of the parent, which for a compiler is large. The child runs no compiled code, only the few
// instructions in `startChild`, on the parent's stack without pushing anything, and the kernel
// holds the parent until the child has exec'd. A failed `execve` is reported back through a word
// of shared memory, so a missing or unrunnable program comes back from `spawnProcess` as an
// errno instead of a child that silently exits 127.
#include <{sys, core, mem, heap, file, option, result, string, vec, chars, path, io, sync}>

// ─── the raw calls ───────────────────────────────────────────────────────────

// clone(CLONE_VM | CLONE_VFORK | SIGCHLD) and, in the child, execve. Answers the child's pid, or
// a negative errno from clone. `ctl` is a block of five words the child reads and writes:
// [0] execve's or chdir's error, written before the child exits; [1..3] fds to dup2 onto 0, 1, 2
// (-1 to inherit); [4] a directory to chdir into, as a C string, or 0.
//
// One `asm` block, not calls to `sys`: between the clone and the execve the child shares this
// process's stack and may not push a frame. The values it needs ride in registers clone ignores
// without the flags that read them (rdx parent_tid, r10 child_tid, r8 tls) and that the syscall
// preserves into the child.
local unsafe startChild path:long argv:long envp:long ctl:long -> long {
    pid: long = 0;
    asm {
        in r8 path;
        in r10 argv;
        in rdx envp;
        in rbx ctl;
        "mov rdi, 0x4111"           // CLONE_VM | CLONE_VFORK | SIGCHLD
        "xor rsi, rsi"              // same stack: the child pushes nothing
        "mov eax, 56"               // clone
        "syscall"
        "test rax, rax"
        "jnz .spawnParent"
        "mov rdi, [rbx + 8]"        // CHILD: dup2(ctl[1], 0) ...
        "test rdi, rdi"
        "js .noIn"
        "xor rsi, rsi"
        "mov eax, 33"
        "syscall"
        ".noIn:"
        "mov rdi, [rbx + 16]"       // ... dup2(ctl[2], 1) ...
        "test rdi, rdi"
        "js .noOut"
        "mov rsi, 1"
        "mov eax, 33"
        "syscall"
        ".noOut:"
        "mov rdi, [rbx + 24]"       // ... dup2(ctl[3], 2)
        "test rdi, rdi"
        "js .noErr"
        "mov rsi, 2"
        "mov eax, 33"
        "syscall"
        ".noErr:"
        "mov rdi, [rbx + 32]"       // chdir(ctl[4])
        "test rdi, rdi"
        "jz .noDir"
        "mov eax, 80"
        "syscall"
        "test rax, rax"
        "js .childFailed"
        ".noDir:"
        "mov rdi, r8"               // execve(path, argv, envp)
        "mov rsi, r10"
        "mov eax, 59"
        "syscall"
        ".childFailed:"
        "mov [rbx], rax"            // only reached on failure: -errno
        "mov rdi, 127"
        "mov eax, 60"               // _exit
        "syscall"
        ".spawnParent:"
        out pid rax;
    }
    return pid;
}

// wait4(pid, &status, 0, NULL), retried over EINTR. Answers the pid reaped, the raw status in
// `status[0]`, or a negative errno.
local waitFor pid:long inout status:[long] -> long {
    loop {
        r: long = 0;
        unsafe { r = syscall4(Syscall.Wait4, pid, status.ptr as long, 0, 0); }
        if (r != -Errno.Intr) { return r; }
    }
}

// ─── how a child ended ───────────────────────────────────────────────────────

// A child either returned an exit code or was killed by a signal, never both.
pub enum ExitStatus {
    Exited(long),       // the code it returned
    Signaled(long)      // the signal that ended it
}

methods ExitStatus {
    success &self -> bool {
        match self { Exited(c) { return c == 0; } Signaled(_) { return false; } }
    }
    exited &self -> bool {
        match self { Exited(_) { return true; } Signaled(_) { return false; } }
    }
    // The exit code, or nothing when a signal ended it.
    code &self -> Option<long> {
        match self { Exited(c) { return Option.Some(c); } Signaled(_) { return Option.None; } }
    }
    // The signal, or nothing when it exited.
    signal &self -> Option<long> {
        match self { Exited(_) { return Option.None; } Signaled(s) { return Option.Some(s); } }
    }
    // "exited with status 1", "was killed by signal 11": the end of a sentence about the child.
    describe &self -> String {
        match self {
            Exited(c)   { return format("exited with status {}", c); }
            Signaled(s) { return format("was killed by signal {}", s); }
        }
    }
}

// The kernel's wait status, decoded: the low seven bits are the terminating signal (0 for a
// normal exit), and the exit code is the byte above them.
local decodeStatus raw:long -> ExitStatus {
    sig: long = raw & 127;
    if (sig == 0) { return ExitStatus.Exited((raw >> 8) & 255); }
    return ExitStatus.Signaled(sig);
}

// ─── a running child ─────────────────────────────────────────────────────────

// Rust's Child. The pipe ends are there when the Command asked for `Stdio.Piped`; `Child { pid }`
// alone is a child with none (an omitted Option is None).
pub struct Child { pid: long, stdin: Option<File>, stdout: Option<File>, stderr: Option<File> }

// What `Command.output` and `Child.waitWithOutput` collect.
pub struct Output { status: ExitStatus, stdout: String, stderr: String }

local SIGKILL: long = 9;
local POLLIN: long = 1;

methods Child {
    id &self -> long { return self.pid; }

    // Block until this child has finished. Its stdin pipe, if any, is closed first, so a child
    // reading to the end of its input is not left waiting. A child is reaped exactly once:
    // waiting on it again, or on a child `waitAnyProcess` already reaped, is ECHILD.
    wait &self -> Result<ExitStatus, long> {
        self.stdin = Option.None;
        raw: [long; 1];
        r: long = waitFor(self.pid, &raw[..]);
        if (r < 0) { return Result.Err(-r); }
        return Result.Ok(decodeStatus(raw[0]));
    }

    kill &self -> Result<long, long> {
        r: long = 0;
        unsafe { r = syscall2(Syscall.Kill, self.pid, SIGKILL); }
        if (r < 0) { return Result.Err(-r); }
        return Result.Ok(0);
    }

    // Everything the child writes to its piped stdout and stderr, then how it ended. Both pipes
    // are read as data arrives, so a child that fills one while the other is being read is not
    // stuck.
    waitWithOutput self -> Result<Output, long> {
        self.stdin = Option.None;
        out: String;
        err: String;
        r: long = drainPipes(&self, &out, &err);
        if (r < 0) { return Result.Err(-r); }
        st: Result<ExitStatus, long> = self.wait();
        match st {
            Ok(s)  { return Result.Ok(Output { status: s, stdout: out, stderr: err }); }
            Err(e) { return Result.Err(e); }
        }
    }
}

local fdOf inout o:Option<File> -> long {
    match o { Some(f) { return f.fd as long; } None { return -1; } }
}
local putInt32 inout b:[u8] at:long v:long -> void {
    for k in 0..4 { b[at + k] = ((v >> (8 * k)) & 255) as u8; }
}

// Read the child's stdout and stderr pipes until both reach their end. 0, or a negative errno.
local drainPipes inout c:Child inout out:String inout err:String -> long {
    outFd: long = fdOf(&c.stdout);
    errFd: long = fdOf(&c.stderr);
    chunk: [u8; 4096];
    while (outFd >= 0 || errFd >= 0) {
        pfd: [u8; 16];                       // two struct pollfd; a negative fd is skipped
        putInt32(&pfd[..], 0, outFd);
        pfd[4] = POLLIN as u8;
        putInt32(&pfd[..], 8, errFd);
        pfd[12] = POLLIN as u8;
        r: long = 0;
        unsafe { r = syscall3(Syscall.Poll, &pfd as long, 2, -1); }
        if (r == -Errno.Intr) { continue; }
        if (r < 0) { return r; }
        if (outFd >= 0 && pfd[6] != 0) {
            n: long = 0;
            unsafe { n = syscall3(Syscall.Read, outFd, &chunk as long, 4096); }
            if (n > 0) { out.pushStr(chunk[..n] as str); }
            else if (n != -Errno.Intr) { outFd = -1; }
        }
        if (errFd >= 0 && pfd[14] != 0) {
            n: long = 0;
            unsafe { n = syscall3(Syscall.Read, errFd, &chunk as long, 4096); }
            if (n > 0) { err.pushStr(chunk[..n] as str); }
            else if (n != -Errno.Intr) { errFd = -1; }
        }
    }
    c.stdout = Option.None;
    c.stderr = Option.None;
    return 0;
}

// Block until any child of this process finishes, and say which. Use it to run several children
// and handle whichever finishes first.
pub waitAnyProcess -> Result<(long, ExitStatus), long> {
    raw: [long; 1];
    r: long = waitFor(-1, &raw[..]);
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok((r, decodeStatus(raw[0])));
}

// ─── Command ─────────────────────────────────────────────────────────────────
// Rust's Command: a program, its arguments and environment, and where its standard streams go.
//
//     out: Output = Command.of("git").arg("log").arg("-1").output().unwrap();
//     if (out.status.success()) { print("{}", out.stdout); }
//
//     c: Child = Command.of("sort").stdin(Stdio.Piped).stdout(Stdio.Piped).spawn().unwrap();

pub enum Stdio: long { Inherit = 0, Piped = 1, Null = 2 }

pub struct Command {
    program: String, args: Vec<String>, envSet: Vec<String>, clearEnv: bool, dir: String,
    inMode: Option<Stdio>, outMode: Option<Stdio>, errMode: Option<Stdio>
}

local O_RDWR: long = 2;
local O_CLOEXEC: long = 0x80000;

methods Command {
    of program:str -> Command {
        a: Vec<String>;
        e: Vec<String>;
        d: String;
        return Command { program: stringOf(program), args: a, envSet: e, clearEnv: false, dir: d,
                         inMode: Option.None, outMode: Option.None, errMode: Option.None };
    }
    arg self a:str -> Command { self.args.push(stringOf(a)); return self; }
    args self xs:Vec<str> -> Command { for x in xs { self.args.push(stringOf(x)); } return self; }
    // Set NAME=value in the child's environment, over whatever it inherits.
    env self name:str value:str -> Command { self.envSet.push(format("{}={}", name, value)); return self; }
    // Start the child with no environment but what `env` sets.
    envClear self -> Command { self.clearEnv = true; return self; }
    currentDir self dir:str -> Command { self.dir = stringOf(dir); return self; }
    stdin  self s:Stdio -> Command { self.inMode = Option.Some(s); return self; }
    stdout self s:Stdio -> Command { self.outMode = Option.Some(s); return self; }
    stderr self s:Stdio -> Command { self.errMode = Option.Some(s); return self; }

    // Start it. Streams not set are inherited.
    spawn &self -> Result<Child, long> { return self.start(Stdio.Inherit, Stdio.Inherit, Stdio.Inherit); }
    // Start it and wait. Streams not set are inherited.
    status &self -> Result<ExitStatus, long> {
        c: Result<Child, long> = self.spawn();
        match c { Ok(ch) { return ch.wait(); } Err(e) { return Result.Err(e); } }
    }
    // Run it to the end and collect what it wrote. As in Rust, streams not set are: stdin from
    // nothing, stdout and stderr piped back.
    output &self -> Result<Output, long> {
        c: Result<Child, long> = self.start(Stdio.Null, Stdio.Piped, Stdio.Piped);
        match c { Ok(ch) { return ch.waitWithOutput(); } Err(e) { return Result.Err(e); } }
    }

    start &self dIn:Stdio dOut:Stdio dErr:Stdio -> Result<Child, long> {
        modes: [long; 3];
        modes[0] = self.inMode.unwrapOr(dIn) as long;
        modes[1] = self.outMode.unwrapOr(dOut) as long;
        modes[2] = self.errMode.unwrapOr(dErr) as long;
        childFd: [long; 3];                  // what the child gets as 0, 1, 2 (-1: inherit)
        mine: [long; 3];                     // the parent's ends of the pipes (-1: none)
        for k in 0..3 { childFd[k] = -1; mine[k] = -1; }
        failed: long = 0;
        for k in 0..3 {
            if (failed != 0) { break; }
            if (modes[k] == Stdio.Null) {
                nul: [u8; 16];
                toCPath("/dev/null", &nul[..]);
                fd: long = 0;
                unsafe { fd = sysOpen(&nul as long, O_RDWR | O_CLOEXEC, 0); }
                if (fd < 0) { failed = fd; } else { childFd[k] = fd; }
            } else if (modes[k] == Stdio.Piped) {
                p: [u8; 8];
                r: long = 0;
                unsafe { r = syscall2(Syscall.Pipe2, &p as long, O_CLOEXEC); }
                if (r < 0) { failed = r; }
                else {
                    rd: long = (p[0] as long) | ((p[1] as long) << 8) | ((p[2] as long) << 16) | ((p[3] as long) << 24);
                    wr: long = (p[4] as long) | ((p[5] as long) << 8) | ((p[6] as long) << 16) | ((p[7] as long) << 24);
                    if (k == 0) { childFd[k] = rd; mine[k] = wr; } else { childFd[k] = wr; mine[k] = rd; }
                }
            }
        }
        pid: long = failed;
        if (failed == 0) {
            argv: Vec<str>;
            env: Vec<str>;
            unsafe {
                for a in self.args { argv.push(a.view()); }
                if (!self.clearEnv) { env = environment(); }
                for s in self.envSet { setEnvEntry(&env, s.view()); }
                pid = launch(self.program.view(), argv, env, childFd[..], self.dir.view());
            }
        }
        for k in 0..3 { if (childFd[k] >= 0) { sysClose(childFd[k]); } }
        if (pid < 0) {
            for k in 0..3 { if (mine[k] >= 0) { sysClose(mine[k]); } }
            return Result.Err(-pid);
        }
        return Result.Ok(Child { pid: pid, stdin: pipeEnd(mine[0]), stdout: pipeEnd(mine[1]), stderr: pipeEnd(mine[2]) });
    }
}

local pipeEnd fd:long -> Option<File> {
    if (fd < 0) { return Option.None; }
    return Option.Some(File { fd: fd as int });
}

// Replace the entry for the same NAME, or add one.
local setEnvEntry inout env:Vec<str> entry:str -> void {
    eq: long = strFind(entry, "=").unwrapOr(entry.len);
    for i in 0..env.len() {
        e: str = env.get(i);
        if (e.len > eq && charAt(e, eq) == '=' && strStartsWith(e, entry[..eq])) { env.set(i, entry); return; }
    }
    env.push(entry);
}

// ─── starting one ────────────────────────────────────────────────────────────

// Start `program` with `args` (not counting the program itself, which becomes argv[0]), in this
// process's environment. Errors are errnos: ENOENT when nothing on PATH has that name, otherwise
// whatever clone or execve said.
pub spawnProcess program:str args:Vec<str> -> Result<Child, long> {
    return spawnProcessEnv(program, args, environment());
}

// The same, with the child's environment given outright as `NAME=value` strings. PATH lookup
// still reads this process's PATH: the program is found here, then run there.
pub spawnProcessEnv program:str args:Vec<str> env:Vec<str> -> Result<Child, long> {
    fds: [long; 3];
    for k in 0..3 { fds[k] = -1; }
    pid: long = launch(program, args, env, fds[..], "");
    if (pid < 0) { return Result.Err(-pid); }
    return Result.Ok(Child { pid: pid });
}

// The pid, or a negative errno. `fds`: what the child gets as 0, 1, 2 (-1 to inherit); `dir`: a
// directory to start in ("" for this one's).
local launch program:str args:Vec<str> env:Vec<str> fds:[long] dir:str -> long {
    flush();                                // what this process printed goes before the child's
    found: Option<String> = findProgram(program);
    path: String;
    match found {
        Some(p) { path = p; }
        None    { return -Errno.NoEnt; }
    }
    // One block holds both pointer arrays, the five control words and every string they point
    // at, each NUL-terminated. Built before the clone and freed after it, which is safe because
    // the parent does not run again until the child has exec'd or exited.
    argc: long = args.len() + 1;
    envc: long = env.len();
    bytes: long = path.length() + 1 + program.len + 1 + dir.len + 1;
    for x in args { bytes = bytes + x.len + 1; }
    for e in env { bytes = bytes + e.len + 1; }
    words: long = argc + 1 + envc + 1 + 5;
    block: long = malloc(words * 8 + bytes);
    pid: long = 0;
    err: long = 0;
    unsafe {
        argv: *long = block as *long;
        envp: *long = argv + argc + 1;
        ctl: *long = envp + envc + 1;
        ctl[0] = 0;
        for k in 0..3 { ctl[k + 1] = fds[k]; }
        at: long = (ctl + 5) as long;
        ctl[4] = 0;
        if (dir.len > 0) { ctl[4] = at; at = putCString(at, dir); }
        cpath: long = at;
        at = putCString(at, path.view());
        argv[0] = at;
        at = putCString(at, program);
        for k in 0..args.len() {
            argv[k + 1] = at;
            at = putCString(at, args.get(k));
        }
        argv[argc] = 0;
        for k in 0..envc {
            envp[k] = at;
            at = putCString(at, env.get(k));
        }
        envp[envc] = 0;
        pid = startChild(cpath, argv as long, envp as long, ctl as long);
        err = ctl[0];
        free(block);
    }
    if (pid < 0) { return pid; }
    if (err < 0) {
        // The child never became the program: reap it so it does not linger, and report why.
        raw: [long; 1];
        waitFor(pid, &raw[..]);
        return err;
    }
    return pid;
}

// Start `program` and wait for it.
pub runProcess program:str args:Vec<str> -> Result<ExitStatus, long> {
    c: Result<Child, long> = spawnProcess(program, args);
    match c {
        Ok(child) { return child.wait(); }
        Err(e)    { return Result.Err(e); }
    }
}

// `s` and a NUL at `at`; answers where the next string goes.
local unsafe putCString at:long s:str -> long {
    memcpy(at, s.ptr, s.len);
    p: *u8 = (at + s.len) as *u8;
    *p = 0;
    return at + s.len + 1;
}

// ─── the environment and PATH ────────────────────────────────────────────────

// The text of /proc/self/environ, read on first use and kept for the life of the process. It is
// never written again, so the views below can safely point into it. It comes from that file
// because the startup code passes `main` only its arguments, and the file holds the environment
// the process started with. The first use can come from several threads at once, so the read
// is made under a lock: one thread fills the text, and the rest wait for it and then share it.
struct Environ { text: String, read: bool }
var gEnviron: Mutex<Environ> = Mutex { sl: SpinLock.new(), data: Environ { text: String.new(), read: false } };

local environText -> str {
    view: str = "";
    with gEnviron {
        if (!gEnviron.data.read) {
            readWhole("/proc/self/environ", &gEnviron.data.text);
            gEnviron.data.read = true;
        }
        unsafe { view = gEnviron.data.text.view(); }
    }
    return view;
}

// This process's environment as `NAME=value` strings: views into the text above.
pub environment -> Vec<str> {
    out: Vec<str>;
    text: str = environText();
    start: long = 0;
    for i in 0..text.len {
        if (charAt(text, i) == 0) {
            if (i > start) { out.push(strSlice(text, start, i - start)); }
            start = i + 1;
        }
    }
    if (start < text.len) { out.push(strSlice(text, start, text.len - start)); }
    return out;
}

// The value of one environment variable, if it is set.
pub envVar name:str -> Option<str> {
    env: Vec<str> = environment();
    for e in env {
        if (e.len > name.len && charAt(e, name.len) == '=' && strStartsWith(e, name)) {
            return Option.Some(strSlice(e, name.len + 1, e.len - name.len - 1));
        }
    }
    return Option.None;
}

// Where `name` would run from: itself when it holds a `/` (taken as written, so that starting it
// reports whatever `execve` makes of it), otherwise the first directory on PATH holding an
// executable of that name. An empty PATH entry means the current directory, as POSIX has it.
pub findProgram name:str -> Option<String> {
    if (name.len == 0) { return Option.None; }
    if (strContains(name, "/")) { return Option.Some(stringOf(name)); }
    path: str = "/usr/local/bin:/usr/bin:/bin";
    set: Option<str> = envVar("PATH");
    match set { Some(p) { path = p; } None { } }
    dirs: Vec<str> = strSplit(path, ':');
    for dir in dirs {
        cand: String;
        if (dir.len > 0) { cand.pushStr(dir); } else { cand.pushStr("."); }
        cand.push('/');
        cand.pushStr(name);
        ok: bool = false;
        unsafe { ok = isExecutable(cand.view()); }
        if (ok) { return Option.Some(cand); }
    }
    return Option.None;
}

local isExecutable path:str -> bool {
    buf: [u8; PATH_MAX];
    if (toCPath(path, &buf[..]) < 0) { return false; }
    unsafe { return sysAccess(&buf, 1) == 0; }  // X_OK
}

// The whole of a file, appended to `out`, reading until the end rather than sizing it first:
// /proc files report a size of zero.
local readWhole path:str inout out:String -> void {
    o: Result<File, long> = File.openRead(path);
    match o {
        Err(_) { }
        Ok(f) {
            loop {
                out.reserve(4096);
                n: long = 0;
                unsafe { n = f.readInto((out.buf as long) + out.len, out.cap - out.len); }
                if (n <= 0) { break; }
                out.len += n;
                if (out.len < out.cap) { break; }
            }
        }
    }
}
