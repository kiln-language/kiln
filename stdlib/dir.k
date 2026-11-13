// Directories: making, removing, walking, and where you are.
//
//     d: Result<Dir, long> = openDir(".");
//     match d {
//         Ok(dd) {
//             e: Option<DirEntry> = dd.nextReal();
//             while (e.isSome()) {
//                 en: DirEntry = e.unwrap();
//                 println("{} {}", en.kindName(), en);
//                 e = dd.nextReal();
//             }
//         }
//         Err(errno) { println("cannot open: {}", errno); }
//     }
//
// A `Dir` owns its fd and a read buffer, and releases both on Drop. Reading is batched: one
// `getdents64` fills the buffer with many variable-length records and `next` walks them, so
// listing a large directory is a handful of syscalls rather than one per name.
#include <{sys, core, mem, path, heap, io, file, option, result, string, vec, bytes, pathbuf}>

local NAME_MAX:  long = 256;    // NAME_MAX is 255, plus the terminator
local BUF_BYTES: long = 32768;  // one getdents64 batch

// O_RDONLY | O_DIRECTORY: refuses to open a plain file as a directory, so a bad path is an
// error here rather than a stream of nonsense records later.
local OPEN_DIR_FLAGS: long = 0x10000;

// The permission bits a new directory gets, when the caller does not say: 0755, since a
// directory has to be traversable to be useful.
pub DIR_MODE: long = 0x1ED;

// The `d_type` byte of a directory record. Unknown is a real answer, not a failure: some
// filesystems do not carry the type in the directory and want a stat to tell you.
pub enum EntryKind: u8 {
    Unknown = 0,
    Fifo    = 1,
    CharDev = 2,
    Folder  = 4,
    BlockDev = 6,
    File    = 8,
    Link    = 10,
    Socket  = 12
}

// One name from a directory. The name is COPIED into the entry rather than pointed at the
// read buffer, which the next batch overwrites — an entry you are still holding would
// otherwise change under you, silently, and only for large directories.
pub struct DirEntry {
    name: [u8; NAME_MAX],
    len:  long,
    kind: EntryKind
}

methods DirEntry {
    length &self -> long { return self.len; }
    kind   &self -> EntryKind { return self.kind; }
    isDir  &self -> bool { return self.kind == EntryKind.Folder; }
    isFile &self -> bool { return self.kind == EntryKind.File; }
    // `.` or `..`: every directory has both, and almost no caller wants them.
    isDots &self -> bool {
        return self.name[0] == '.' && (self.len == 1 || (self.len == 2 && self.name[1] == '.'));
    }
    // Is this entry named `s`?
    named &self s:str -> bool { return bytesEqual(self.name[..self.len], s as [u8]); }

    // A view of the name, valid while this entry is. `unsafe` for the same reason
    // `String.view` is: nothing stops the view outliving what it points into.
    unsafe view &self -> str { return self.name[..self.len] as str; }
    // The name as a String of its own, which outlives the entry.
    nameString &self -> String {
        s: String;
        s.pushStr(self.name[..self.len] as str);
        return s;
    }

    // Four columns wide, so a listing lines up.
    kindName &self -> str {
        if (self.kind == EntryKind.Folder)   { return "dir "; }
        if (self.kind == EntryKind.File)     { return "file"; }
        if (self.kind == EntryKind.Link)     { return "link"; }
        if (self.kind == EntryKind.Socket)   { return "sock"; }
        if (self.kind == EntryKind.Fifo)     { return "fifo"; }
        if (self.kind == EntryKind.CharDev)  { return "chr "; }
        if (self.kind == EntryKind.BlockDev) { return "blk "; }
        return "?   ";
    }
}

// So `println("{}", entry)` prints the name, without handing out a view of it.
methods DirEntry for Display {
    display &self w:Write -> void { putStr(w, self.name[..self.len] as str); }
}

// An open directory, part-read. `used` is how many bytes the last batch returned and `pos`
// how far through them `next` has walked; pos == used means the buffer is spent.
pub struct Dir {
    fd:   int,
    buf:  *u8,
    used: long,
    pos:  long
}

methods Dir for Default {
    new -> Dir { unsafe { return Dir { fd: -1, buf: 0 as *u8, used: 0, pos: 0 }; } }
}

methods Dir for Drop {
    drop &self -> void {
        self.close();
        unsafe { free(self.buf as long); self.buf = 0 as *u8; }   // free(0) is a no-op
    }
}

methods Dir {
    isOpen &self -> bool { return self.fd >= 0; }

    close &self -> void {
        if (self.fd >= 0) { sysClose(self.fd); self.fd = -1; }
    }

    // The next name, or None at the end of the directory. Refills the buffer when it runs
    // out, which is where the syscall happens; every other call is a walk over bytes we hold.
    next &self -> Option<DirEntry> {
        if (self.fd < 0) { return Option.None; }
        if (self.pos >= self.used) {
            n: long = 0;
            unsafe { n = syscall3(Syscall.Getdents64, self.fd, self.buf as long, BUF_BYTES); }
            if (n <= 0) { return Option.None; }      // 0 = end, negative = -errno
            self.used = n;
            self.pos = 0;
        }
        e: DirEntry;
        unsafe {
            b: *u8 = self.buf + self.pos;
            // struct linux_dirent64 { u64 ino; s64 off; u16 reclen @16; u8 type @18; char name[] @19 }
            reclen: long = (b[16] as long) | ((b[17] as long) << 8);
            e.kind = b[18] as EntryKind;
            // The name is NUL-terminated and padded to reclen, so scan rather than subtract.
            cap: long = reclen - 19;
            if (cap > NAME_MAX - 1) { cap = NAME_MAX - 1; }
            k: long = 0;
            while (k < cap && b[19 + k] != 0) {
                e.name[k] = b[19 + k];
                k = k + 1;
            }
            e.len = k;
            self.pos = self.pos + reclen;
            if (e.kind == EntryKind.Unknown) {
                // The filesystem left the type out: ask (without following a link), relative to
                // this directory. S_IFMT >> 12 is the d_type.
                e.name[k] = 0;
                st: [u8; 144];
                r: long = syscall4(Syscall.Newfstatat, self.fd, &e.name as long, &st as long, 0x100);
                if (r == 0) { e.kind = (((st[25] as long) >> 4) & 15) as EntryKind; }
            }
        }
        return Option.Some(e);
    }

    // The next name that is not `.` or `..`.
    nextReal &self -> Option<DirEntry> {
        loop {
            o: Option<DirEntry> = self.next();
            match o {
                Some(e) { if (!e.isDots()) { return Option.Some(e); } }
                None    { return Option.None; }
            }
        }
    }
}

// ─── opening and the one-shot operations ────────────────────────────────────

// A path syscall's answer as a Result: the path is refused before the call when it cannot be
// passed as written, and a negative answer becomes the positive errno.
local onPath path:str nr:Syscall arg:long -> Result<long, long> {
    buf: [u8; PATH_MAX];
    if (toCPath(path, &buf[..]) < 0) { return Result.Err(Errno.NameTooLong); }
    r: long = 0;
    unsafe { r = syscall2(nr, &buf as long, arg); }
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(r);
}

pub openDir path:str -> Result<Dir, long> {
    buf: [u8; PATH_MAX];
    if (toCPath(path, &buf[..]) < 0) { return Result.Err(Errno.NameTooLong); }
    fd: long = 0;
    unsafe { fd = sysOpen(&buf, OPEN_DIR_FLAGS, 0); }
    if (fd < 0) { return Result.Err(-fd); }
    mem: long = malloc(BUF_BYTES);
    unsafe { return Result.Ok(Dir { fd: fd as int, buf: mem as *u8, used: 0, pos: 0 }); }
}

// A new directory, mode 0755.
pub makeDir path:str -> Result<long, long> { return makeDirMode(path, DIR_MODE); }
// The same with the permission bits chosen (the process umask still applies).
pub makeDirMode path:str mode:long -> Result<long, long> { return onPath(path, Syscall.Mkdir, mode); }

// `path` and every missing directory above it, the way `mkdir -p` does: a component that already
// exists is fine, anything else that goes wrong is the answer.
pub makeDirAll path:str -> Result<long, long> {
    parts: Vec<str> = splitPath(path);
    sofar: String;
    if (isAbsolute(path)) { sofar.push('/'); }
    for i in 0..parts.len() {
        if (i > 0) { sofar.push('/'); }
        sofar.pushStr(parts.get(i));
        r: Result<long, long> = Result.Ok(0);
        unsafe { r = makeDir(sofar.view()); }
        match r {
            Ok(_)  { }
            Err(e) { if (e != Errno.Exist) { return Result.Err(e); } }
        }
    }
    return Result.Ok(0);
}

// Only an EMPTY directory; removing a populated one is a walk, and a walk that deletes should
// be written where you can see it.
pub removeDir path:str -> Result<long, long> { return onPath(path, Syscall.Rmdir, 0); }

pub changeDir path:str -> Result<long, long> { return onPath(path, Syscall.Chdir, 0); }

// Move or rename. Atomic within one filesystem, and refused (EXDEV) across two.
pub renamePath from:str to:str -> Result<long, long> {
    a: [u8; PATH_MAX];
    b: [u8; PATH_MAX];
    if (toCPath(from, &a[..]) < 0 || toCPath(to, &b[..]) < 0) { return Result.Err(Errno.NameTooLong); }
    r: long = 0;
    unsafe { r = syscall2(Syscall.Rename, &a as long, &b as long); }
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(0);
}

local onTwoPaths a:str b:str nr:Syscall -> Result<long, long> {
    x: [u8; PATH_MAX];
    y: [u8; PATH_MAX];
    if (toCPath(a, &x[..]) < 0 || toCPath(b, &y[..]) < 0) { return Result.Err(Errno.NameTooLong); }
    r: long = 0;
    unsafe { r = syscall2(nr, &x as long, &y as long); }
    if (r < 0) { return Result.Err(-r); }
    return Result.Ok(0);
}

// `link` becomes another name for `original` (Rust's fs::hard_link).
pub hardLink original:str link:str -> Result<long, long> { return onTwoPaths(original, link, Syscall.Link); }
// `link` becomes a symlink holding `original` (Rust's os::unix::fs::symlink).
pub softLink original:str link:str -> Result<long, long> { return onTwoPaths(original, link, Syscall.Symlink); }
// What a symlink holds.
pub readLink path:str -> Result<String, long> {
    p: [u8; PATH_MAX];
    if (toCPath(path, &p[..]) < 0) { return Result.Err(Errno.NameTooLong); }
    out: [u8; PATH_MAX];
    n: long = 0;
    unsafe { n = syscall3(Syscall.Readlink, &p as long, &out as long, PATH_MAX); }
    if (n < 0) { return Result.Err(-n); }
    s: String;
    s.pushStr(out[..n] as str);
    return Result.Ok(s);
}
// The permission bits of `path`, e.g. 0o755.
pub setPermissions path:str mode:long -> Result<long, long> { return onPath(path, Syscall.Chmod, mode); }

// Rust's fs::copy: the bytes and the permission bits, replacing `to`. The count copied. The
// kernel copies in place (copy_file_range) where it can; read/write where it cannot.
pub copyFile from:str to:str -> Result<long, long> {
    r1: Result<File, long> = File.openRead(from);
    if (r1.isErr()) { return Result.Err(r1.unwrapErr()); }
    src: File = r1.unwrap();
    md: Result<Metadata, long> = src.metadata();
    if (md.isErr()) { return Result.Err(md.unwrapErr()); }
    perms: long = md.unwrap().permissions();
    r2: Result<File, long> = File.create(to);
    if (r2.isErr()) { return Result.Err(r2.unwrapErr()); }
    dst: File = r2.unwrap();
    pr: Result<long, long> = dst.setPermissions(perms);
    s: long = src.fd as long;
    d: long = dst.fd as long;
    copied: long = 0;
    loop {
        n: long = 0;
        unsafe { n = syscall6(Syscall.CopyFileRange, s, 0, d, 0, 1 << 30, 0); }
        if (n == -Errno.Intr) { continue; }
        if (n == 0) { return Result.Ok(copied); }
        if (n < 0) {
            if (copied == 0 && (n == -Errno.XDev || n == -Errno.NoSys || n == -Errno.Inval || n == -Errno.OpNotSupp)) { break; }
            return Result.Err(-n);
        }
        copied = copied + n;
    }
    chunk: [u8; 16384];
    loop {
        n: long = src.readSome(&chunk[..]);
        if (n < 0) { return Result.Err(-n); }
        if (n == 0) { return Result.Ok(copied); }
        w: long = dst.writeBytes(chunk[..n]);
        if (w < 0) { return Result.Err(-w); }
        copied = copied + n;
    }
    return Result.Ok(copied);
}

// The working directory, as a String you own. getcwd(2) returns the length INCLUDING the
// terminator, which is not part of the text.
pub currentDir -> Result<String, long> {
    buf: [u8; PATH_MAX];
    n: long = 0;
    unsafe { n = syscall2(Syscall.Getcwd, &buf as long, PATH_MAX); }
    if (n < 0) { return Result.Err(-n); }
    s: String;
    s.pushStr(buf[..n - 1] as str);
    return Result.Ok(s);
}

pub dirExists path:str -> bool {
    d: Result<Dir, long> = openDir(path);
    return d.isOk();
}

// Every name in `path` but `.` and `..`, in the order the filesystem gives them (no particular
// one), each a String of its own.
pub listDir path:str -> Result<Vec<String>, long> {
    d: Result<Dir, long> = openDir(path);
    match d {
        Err(e) { return Result.Err(e); }
        Ok(dd) {
            out: Vec<String>;
            loop {
                o: Option<DirEntry> = dd.nextReal();
                match o {
                    Some(e) { out.push(e.nameString()); }
                    None    { return Result.Ok(out); }
                }
            }
        }
    }
}
