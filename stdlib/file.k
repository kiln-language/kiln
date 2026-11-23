// `File`: an owning handle around a file descriptor. It implements `Write` and `Read`, so the
// formatter and any sink/source machinery target it like any other, and `Drop` closes the fd at
// scope exit, so an opened file is released even on an early `return`.
//
// Opening a file and whole-file operations return `Result<_, long>`, where the error is a
// positive errno. Result is `MustUse`, so the check cannot be forgotten.
//
// The per-call methods on an open handle (write, read, seek, flush) stay on the syscall
// convention, returning a count or a negative errno. That is not a second opinion about error
// handling: `Write` and `Read` declare `-> long`, so those two are fixed, and having `seek`
// disagree with the `write` beside it would be worse than one convention per layer.
#include <{sys, core, mem, path, result}>

// Is `fd` a terminal? Only a terminal answers TCGETS, the call that reads its settings.
pub isTerminal fd:long -> bool {
    settings: [u8; 64];                              // the kernel's struct termios is 36 bytes
    unsafe { return syscall3(Syscall.Ioctl, fd, 0x5401, &settings[0] as long) == 0; }
}

// ─── settings ───────────────────────────────────────────────────────────────
// The access mode is the low two bits of open(2)'s flags: pick exactly one and OR the
// OpenFlag bits onto it.
pub enum Access: long { Read = 0, Write = 1, ReadWrite = 2 }

// open(2) behaviour bits, combined with `|`. `None` is the neutral element.
pub enum OpenFlag: long {
    None      = 0,
    Create    = 0x40,      // O_CREAT: create the file if it does not exist
    Exclusive = 0x80,      // O_EXCL: with Create, fail if it already exists
    Truncate  = 0x200,     // O_TRUNC: truncate to zero length on open
    Append    = 0x400,     // O_APPEND: every write seeks to end-of-file first
    NonBlock  = 0x800,     // O_NONBLOCK
    Sync      = 0x101000   // O_SYNC: writes reach stable storage before returning
}

pub enum Seek: long { Set = 0, Cur = 1, End = 2 }

// Permission bits for a newly created file, consulted only when Create actually makes one.
pub enum Perm: long { Default = 0x1A4, Private = 0x180, All = 0x1FF }   // 0644, 0600, 0777

// A path as the kernel wants it, in `buf`; false when it cannot be passed on as written (too
// long, or holding a NUL). Every caller answers that with ENAMETOOLONG.
local cPath path:str inout buf:[u8] -> bool { return toCPath(path, buf) >= 0; }

// ─── File ───────────────────────────────────────────────────────────────────
pub struct File { fd: int }

// Rust's fs::Metadata: what stat(2) says about a file. Times are nanoseconds since the Unix epoch.
pub struct Metadata {
    mode: long, size: long, dev: long, ino: long, nlink: long, uid: long, gid: long, blocks: long,
    accessedNs: long, modifiedNs: long, changedNs: long
}
local STAT_SIZE: long = 144;               // struct stat on x86-64

// A default File is closed, so `f: File;` is a safe placeholder whose drop is a no-op.
methods File for Default {
    new -> File { return File { fd: -1 }; }
}

methods File {
    // The general form: an access mode, any OpenFlag bits OR'd together, and the permission
    // bits a created file gets.
    open path:str access:Access flags:long mode:long -> Result<File, long> {
        buf: [u8; PATH_MAX];
        if (!cPath(path, &buf[..])) { return Result.Err(Errno.NameTooLong); }
        fd: long = 0;
        unsafe { fd = sysOpen(&buf, (access as long) | flags, mode); }   // a variable of an enum type needs the cast; a variant does not
        if (fd < 0) { return Result.Err(-fd); }
        return Result.Ok(File { fd: fd as int });
    }
    // Create or truncate `path` for writing, mode 0644.
    create path:str -> Result<File, long> {
        return File.open(path, Access.Write, OpenFlag.Create | OpenFlag.Truncate, Perm.Default);
    }
    // Create `path` for writing, failing with EEXIST if it is already there: the way to claim a
    // name without a race between checking and creating.
    createNew path:str -> Result<File, long> {
        return File.open(path, Access.Write, OpenFlag.Create | OpenFlag.Exclusive, Perm.Default);
    }
    // Open for writing, creating if needed, with every write positioned at end-of-file.
    append path:str -> Result<File, long> {
        return File.open(path, Access.Write, OpenFlag.Create | OpenFlag.Append, Perm.Default);
    }
    openRead path:str -> Result<File, long> {
        return File.open(path, Access.Read, OpenFlag.None, 0);
    }
    openReadWrite path:str -> Result<File, long> {
        return File.open(path, Access.ReadWrite, OpenFlag.Create, Perm.Default);
    }

    // A default File is closed and a closed one is useless, so this distinguishes the
    // placeholder from a handle. An opened File is open by construction.
    isOpen &self -> bool { return self.fd >= 0; }

    // Returns the resulting absolute offset, or a negative errno.
    seek &self off:long whence:Seek -> long { return sysLseek(self.fd, off, whence); }
    tell &self -> long { return sysLseek(self.fd, 0, Seek.Cur); }
    rewind &self -> void { sysLseek(self.fd, 0, Seek.Set); }
    // Total length (one fstat), or a negative errno.
    size &self -> long {
        m: Result<Metadata, long> = self.metadata();
        match m { Ok(md) { return md.size; } Err(e) { return -e; } }
    }
    metadata &self -> Result<Metadata, long> {
        raw: [u8; STAT_SIZE];
        unsafe { return statResult(syscall2(Syscall.Fstat, self.fd, &raw as long), raw[..]); }
    }

    writeStr &self s:str -> long { unsafe { return writeAll(self.fd, s.ptr, s.len); } }
    // Every byte of `b`, over short writes. The count, or a negative errno.
    writeBytes &self b:[u8] -> long { unsafe { return writeAll(self.fd, b.ptr, b.len); } }
    // Fill as much of `buf` as the file has, over short reads: the count (less than buf.len
    // only at the end of the file), or a negative errno. Safe, since the slice carries its length.
    readSome &self inout buf:[u8] -> long { unsafe { return readAll(self.fd, buf.ptr, buf.len); } }
    // The same into memory the caller vouches for. `unsafe`: writes through a raw pointer.
    unsafe readInto &self buf:long cap:long -> long { return readAll(self.fd, buf, cap); }

    // Force the kernel's buffers to disk.
    flush &self -> long { return sysFsync(self.fd); }
    // The data only, not metadata a later read does not need (Rust's sync_data).
    syncData &self -> Result<long, long> { unsafe { return checked(syscall1(Syscall.Fdatasync, self.fd)); } }
    // Cut to `len` bytes, or extend with zeros to it (Rust's set_len).
    setLen &self len:long -> Result<long, long> { unsafe { return checked(syscall2(Syscall.Ftruncate, self.fd, len)); } }
    // The permission bits, e.g. 0o644 (Rust's set_permissions).
    setPermissions &self mode:long -> Result<long, long> { unsafe { return checked(syscall2(Syscall.Fchmod, self.fd, mode)); } }

    // At `off`, leaving the file position alone (Rust's FileExt): one pread, the count read
    // (0 past the end) or a negative errno.
    readAt &self inout buf:[u8] off:long -> long {
        loop {
            n: long = 0;
            unsafe { n = syscall4(Syscall.Pread64, self.fd, buf.ptr, buf.len, off); }
            if (n != -Errno.Intr) { return n; }
        }
        return 0;
    }
    // All of `b` at `off`, over short writes; the file position is left alone.
    writeAt &self b:[u8] off:long -> long {
        done: long = 0;
        while (done < b.len) {
            n: long = 0;
            unsafe { n = syscall4(Syscall.Pwrite64, self.fd, b.ptr + done, b.len - done, off + done); }
            if (n == -Errno.Intr) { continue; }
            if (n <= 0) { if (done > 0) { return done; } return n; }
            done += n;
        }
        return done;
    }
    // Marks the handle closed, so a later drop or close is a harmless no-op.
    close &self -> void {
        if (self.fd >= 0) { sysClose(self.fd); self.fd = -1; }
    }
}

// The formatter and setStdout/setStderr can target a File directly.
methods File for Write {
    write &self ptr:long len:long -> long { unsafe { return writeAll(self.fd, ptr, len); } }
}
// One read (0 = EOF, negative = -errno); `readSome` is the filling form.
methods File for Read {
    read &self ptr:long len:long -> long { unsafe { return sysRead(self.fd, ptr, len); } }
}
methods File for Drop {
    drop &self -> void { self.close(); }
}

// ─── Metadata ───────────────────────────────────────────────────────────────

local S_IFMT: long = 0xF000;
local enum FileMode: long { Fifo = 0x1000, CharDev = 0x2000, Dir = 0x4000, BlockDev = 0x6000, File = 0x8000, Symlink = 0xA000, Socket = 0xC000 }
local AT_FDCWD: long = -100;
local AT_SYMLINK_NOFOLLOW: long = 0x100;

methods Metadata {
    len       &self -> long { return self.size; }
    isDir     &self -> bool { return (self.mode & S_IFMT) == FileMode.Dir; }
    isFile    &self -> bool { return (self.mode & S_IFMT) == FileMode.File; }
    isSymlink &self -> bool { return (self.mode & S_IFMT) == FileMode.Symlink; }
    // The permission bits (0o7777: rwx for owner, group, others, plus setuid/setgid/sticky).
    permissions &self -> long { return self.mode & 0xFFF; }
    readonly    &self -> bool { return (self.mode & 0x92) == 0; }      // no w bit anywhere
}

local word raw:[u8] at:long -> long {
    v: long = 0;
    for k in 0..8 { v = v | ((raw[at + k] as long) << (8 * k)); }
    return v;
}
local statResult r:long raw:[u8] -> Result<Metadata, long> {
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(Metadata {
        dev: word(raw, 0), ino: word(raw, 8), nlink: word(raw, 16),
        mode: word(raw, 24) & 0xFFFFFFFF, uid: word(raw, 28) & 0xFFFFFFFF, gid: word(raw, 32) & 0xFFFFFFFF,
        size: word(raw, 48), blocks: word(raw, 64),
        accessedNs: word(raw, 72) * 1000000000 + word(raw, 80),
        modifiedNs: word(raw, 88) * 1000000000 + word(raw, 96),
        changedNs:  word(raw, 104) * 1000000000 + word(raw, 112)
    });
}
local statAt path:str flags:long -> Result<Metadata, long> {
    buf: [u8; PATH_MAX];
    if (!cPath(path, &buf[..])) { return Result.Err(Errno.NameTooLong); }
    raw: [u8; STAT_SIZE];
    unsafe { return statResult(syscall4(Syscall.Newfstatat, AT_FDCWD, &buf as long, &raw as long, flags), raw[..]); }
}

// Following symlinks to what they name.
pub metadata path:str -> Result<Metadata, long> { return statAt(path, 0); }
// The link itself, not what it names.
pub symlinkMetadata path:str -> Result<Metadata, long> { return statAt(path, AT_SYMLINK_NOFOLLOW); }

// ─── free helpers ───────────────────────────────────────────────────────────

// A syscall's answer as a Result: Ok with the value, or Err with the positive errno.
local checked r:long -> Result<long, long> {
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(r);
}

// Ok carries nothing useful; the point is that a failure cannot be ignored.
pub removeFile path:str -> Result<long, long> {
    buf: [u8; PATH_MAX];
    if (!cPath(path, &buf[..])) { return Result.Err(Errno.NameTooLong); }
    unsafe { return checked(sysUnlink(&buf)); }
}
pub fileExists path:str -> bool {
    buf: [u8; PATH_MAX];
    if (!cPath(path, &buf[..])) { return false; }
    unsafe { return sysAccess(&buf, 0) == 0; }
}
// Open, read up to `cap` bytes, close. Ok is the count. `unsafe`: fills memory at the
// caller's raw pointer.
pub unsafe readFile path:str buf:long cap:long -> Result<long, long> {
    o: Result<File, long> = File.openRead(path);
    match o {
        Err(e) { return Result.Err(e); }
        Ok(f)  { return checked(f.readInto(buf, cap)); }
    }
}
// Write `s` to `path` through a file opened by `open`, then close it. Ok is the count.
local putWhole o:Result<File, long> s:str -> Result<long, long> {
    match o {
        Err(e) { return Result.Err(e); }
        Ok(f)  { return checked(f.writeStr(s)); }
    }
}
// Create or truncate, write, close. Ok is the count. `unsafe`: reads from the caller's pointer.
pub unsafe writeFile path:str ptr:long len:long -> Result<long, long> {
    b: [u8] = (ptr as *u8)[..len];
    return writeFileStr(path, b as str);
}
pub writeFileStr path:str s:str -> Result<long, long> { return putWhole(File.create(path), s); }
// Add `s` to the end of `path`, creating it if needed.
pub appendFileStr path:str s:str -> Result<long, long> { return putWhole(File.append(path), s); }
