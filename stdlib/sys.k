// Raw Linux syscalls. Every one returns the kernel's value directly: a negative return is
// `-errno`, which is the error convention the rest of the stdlib is built on.
//
// There is one way in: `syscall0` .. `syscall6`, the number and the arguments in the registers
// the kernel reads them from. Every module that talks to the kernel calls those with a
// `Syscall` number, rather than carrying an `asm` block of its own per call. The handful of
// named wrappers below are the calls several modules make.
//
// The unsafe boundary follows one rule: a call that reads or writes memory at a
// caller-provided address (a buffer, a path) is an `unsafe` function; one taking only scalars
// is safe, with the raw call in an internal `unsafe { }` block. The `syscallN` entries
// themselves are all unsafe, since the number decides what the arguments mean.

// The x86-64 syscall numbers the library uses. A plain backed enum whose variants are the
// numbers, so `syscall1(Syscall.Close, fd)` costs the same as a hard-coded `mov rax, 3`.
pub enum Syscall: long {
    Read = 0, Write = 1, Open = 2, Close = 3, Fstat = 5, Poll = 7, Lseek = 8, Mmap = 9, Munmap = 11,
    Ioctl = 16, Dup2 = 33, Newfstatat = 262, Dup3 = 292, Pipe2 = 293, Getrandom = 318,
    Mprotect = 10, Mremap = 25, Pread64 = 17, Pwrite64 = 18, Fdatasync = 75, Ftruncate = 77, Link = 86,
    Symlink = 88, Readlink = 89, Chmod = 90, Fchmod = 91, SchedGetaffinity = 204, CopyFileRange = 326,
    SchedYield = 24, Access = 21, Nanosleep = 35, Getpid = 39,
    Socket = 41, Connect = 42, Accept = 43, Sendto = 44, Recvfrom = 45, Shutdown = 48, Bind = 49,
    Listen = 50, Getsockname = 51, Getpeername = 52, Setsockopt = 54, Getsockopt = 55,
    Clone = 56, Execve = 59, Fcntl = 72, EpollWait = 232, EpollCtl = 233, Accept4 = 288, EpollCreate1 = 291,
    Exit = 60, Wait4 = 61, Kill = 62, Fsync = 74, Getcwd = 79, Chdir = 80, Rename = 82,
    Mkdir = 83, Rmdir = 84, Unlink = 87, ArchPrctl = 158, Gettid = 186, Futex = 202,
    Getdents64 = 217, ClockGettime = 228, ExitGroup = 231, Tgkill = 234
}

// The errno values the library tests for by name. A call answers `-errno`, so a check reads
// `if (r == -Errno.Intr)`.
pub enum Errno: long {
    Perm = 1, NoEnt = 2, Srch = 3, Intr = 4, Io = 5, BadF = 9, Child = 10, Again = 11,
    NoMem = 12, Acces = 13, Fault = 14, Exist = 17, NotDir = 20, IsDir = 21, Inval = 22,
    XDev = 18, NoSpc = 28, Pipe = 32, Range = 34, NameTooLong = 36, NoSys = 38, NotEmpty = 39,
    OpNotSupp = 95,
    AfNoSupport = 97, AddrInUse = 98, AddrNotAvail = 99, NetUnreach = 101, ConnAborted = 103,
    ConnReset = 104, NotConn = 107, TimedOut = 110, ConnRefused = 111, InProgress = 115
}

// ─── the entry points ────────────────────────────────────────────────────────
// The `syscall` builtin (core.k) is the kernel call; these keep the typed number.

pub unsafe syscall0 nr:Syscall -> long { return syscall(nr as long); }
pub unsafe syscall1 nr:Syscall a:long -> long { return syscall(nr as long, a); }
pub unsafe syscall2 nr:Syscall a:long b:long -> long { return syscall(nr as long, a, b); }
pub unsafe syscall3 nr:Syscall a:long b:long c:long -> long { return syscall(nr as long, a, b, c); }
pub unsafe syscall4 nr:Syscall a:long b:long c:long d:long -> long { return syscall(nr as long, a, b, c, d); }
pub unsafe syscall6 nr:Syscall a:long b:long c:long d:long e:long f:long -> long {
    return syscall(nr as long, a, b, c, d, e, f);
}

// ─── what several modules call ───────────────────────────────────────────────

// stdout's held bytes, for a panic. io records at startup where its stdout buffer and fill count
// live, so panic.k, which sits below io and must not take stdout's lock (the panicking thread may
// hold it, mid-print), can write them out before its message. Raw addresses rather than a
// function to call: a function whose address is taken could be reached from any indirect call,
// and this one writes stdout by name. All 0 until io sets them, at compile time, and once stdout
// is redirected, which makes `spillStdoutNow` nothing. `@spill`: the compiler's own failed checks
// (an index out of range) call it before their report too.
pub var gStdoutBufAt: long = 0;      // the buffer's first byte
pub var gStdoutPosAt: long = 0;      // the long counting how many bytes it holds
pub var gStdoutCap: long = 0;
@spill pub spillStdoutNow -> void {
    unsafe {
        if (gStdoutPosAt == 0) { return; }
        n: long = *(gStdoutPosAt as *long);
        if (n <= 0 || n > gStdoutCap) { return; }
        writeAll(1, gStdoutBufAt, n);
        *(gStdoutPosAt as *long) = 0;
    }
}

// Ends this thread at once, without the `@fini` hooks (the `exit` builtin runs them). So what
// stdout holds is not written either: a program ending this way after printing to a file or a
// pipe loses it, unless it calls `spillStdoutNow` first, as a panic does.
pub sysExit code:long -> never {
    unsafe { syscall1(Syscall.Exit, code); }
    loop { }
}

pkg unsafe sysWrite fd:long buf:long len:long -> long { return syscall3(Syscall.Write, fd, buf, len); }
pkg unsafe sysRead  fd:long buf:long len:long -> long { return syscall3(Syscall.Read, fd, buf, len); }

// `path` is a NUL-terminated C string, not a `str` (see `path::toCPath`). `flags` is the access
// mode OR'd with the O_* bits; `mode` is consulted only on creation.
pkg unsafe sysOpen path:long flags:long mode:long -> long { return syscall3(Syscall.Open, path, flags, mode); }
pkg unsafe sysUnlink path:long -> long { return syscall1(Syscall.Unlink, path); }
// `mode` 0 = F_OK (existence), 1 = X_OK. Returns 0 if the check succeeds.
pkg unsafe sysAccess path:long mode:long -> long { return syscall2(Syscall.Access, path, mode); }

pkg sysClose fd:long -> long { unsafe { return syscall1(Syscall.Close, fd); } }
// `whence` 0/1/2 = SEEK_SET/CUR/END. Returns the resulting absolute offset.
pkg sysLseek fd:long off:long whence:long -> long { unsafe { return syscall3(Syscall.Lseek, fd, off, whence); } }
// Flush the kernel's buffers for `fd` to the underlying device.
pkg sysFsync fd:long -> long { unsafe { return syscall1(Syscall.Fsync, fd); } }

// Move all `len` bytes, looping over partial transfers and retrying EINTR. A bare read(2) or
// write(2) may move fewer bytes than asked (pipe, socket, full kernel buffer) or be interrupted
// before doing any work, so a single call silently truncates. Every sink flush bottoms out here.
// Returns the total moved (== len, or less only at end of input or when a write makes no
// progress), or a negative errno.
local unsafe transferAll nr:Syscall fd:long buf:long len:long -> long {
    off: long = 0;
    while (off < len) {
        n: long = syscall3(nr, fd, buf + off, len - off);
        if (n > 0) { off = off + n; }
        else if (n == 0) { return off; }          // EOF, or no progress: don't spin
        else if (n != -Errno.Intr) { return n; }  // EINTR is a retry; anything else is real
    }
    return off;
}

pkg unsafe writeAll fd:long buf:long len:long -> long { return transferAll(Syscall.Write, fd, buf, len); }
pkg unsafe readAll  fd:long buf:long len:long -> long { return transferAll(Syscall.Read, fd, buf, len); }

// The kernel's `struct timespec`: what clock_gettime fills and nanosleep reads.
pkg struct Timespec { secs: long, nanos: long }
pkg timespecOf ns:long -> Timespec { return Timespec { secs: ns / 1000000000, nanos: ns % 1000000000 }; }

// Sleep for the whole of `ns` nanoseconds: nanosleep(2), resumed for what was left whenever a
// signal cuts it short. `time.sleepFor` and `thread.sleepNs` are this.
pkg sysSleep ns:long -> void {
    req: Timespec = timespecOf(ns);
    left: Timespec = Timespec { secs: 0, nanos: 0 };
    loop {
        r: long = 0;
        unsafe { r = syscall2(Syscall.Nanosleep, &req as long, &left as long); }
        if (r != -Errno.Intr) { return; }
        req = left;
    }
}
