// The `Write` sink layer under io.k: where bytes go, with buffering, locking and capture as
// composable decorators over it. The formatter targets whichever one it is handed.
#include <{sys, core, mem, bytes}>

// ─── FileOut: a borrowed fd ─────────────────────────────────────────────────
// One writeAll(2) per write, and no Drop — it never closes the fd. Use `File` (file.k) to own
// and manage a descriptor, `FileOut` to compose a sink over one you must not close.
pub struct FileOut { fd: int }
methods FileOut for Default {
    new -> FileOut { return FileOut { fd: 1 }; }    // stdout
}
methods FileOut for Write {
    write &self ptr:long len:long -> long { unsafe { return writeAll(self.fd, ptr, len); } }
}

// ─── BufWriter<W, N>: buffering ─────────────────────────────────────────────
// Coalesces writes into an inline buffer of N bytes (4 KiB unless the type says otherwise) and
// passes them to `inner` when the mode says to, when the buffer fills, when a single write is
// larger than it, or on Drop. `inner` is a concrete W, so `self.inner.write` is a direct call;
// only a leaf reached through a `Write` trait object is dynamic.
//
// The buffer is part of the writer rather than a heap block, which is what lets stdout be built
// at compile time and print without touching the allocator; its size is the type's length
// parameter, so a writer in front of a file can hold more without anything else changing:
//
//     out: BufWriter<File, 65536> = bufWriterWith(f, BufferMode.Block);
//     log: BufWriter<FileOut>     = bufWriter(FileOut { fd: 2 });     // N = 4096
//
// The struct constrains nothing itself — each impl states its own requirement, so `Default`
// needs `W: Default` and the writing impls need `W: Write`, each checked at instantiation.

// When a BufWriter passes what it holds on, besides when the buffer is full.
pub enum BufferMode {
    Block,              // only then: files and pipes, fewest syscalls
    Line(char),         // also whenever a write leaves this byte at the end: '\n' for a terminal
    Delimited(str),     // also whenever a write leaves this text at the end: "\r\n", a prompt's
                        // "> ", a record separator. The text may arrive across several writes.
    Unbuffered          // never hold anything: every write goes straight through
}

// `cap` is how much of `data` is used before a flush: N, unless `setCapacity` lowered it.
pub struct BufWriter<W, N: long = 4096> { inner: W, data: [u8; N], cap: long, pos: long, mode: BufferMode }

methods BufWriter<W: Default, N> for Default {
    new -> BufWriter<W, N> { return BufWriter { inner: W.new(), cap: N, pos: 0, mode: BufferMode.Line('\n') }; }
}
methods BufWriter<W: Write, N> for Write {
    write &self ptr:long len:long -> long {
        if (len > self.cap - self.pos) { self.flush(); }
        if (len > self.cap) { return self.inner.write(ptr, len); }   // bigger than the buffer: through
        unsafe { memcpy(&self.data as long + self.pos, ptr, len); }
        self.pos = self.pos + len;
        if (self.due()) { self.flush(); }
        return len;
    }
}
methods BufWriter<W: Write, N> for Drop {
    drop &self -> void { self.flush(); }            // never lose buffered bytes; `inner` is released after
}
methods BufWriter<W: Write, N> {
    // Pass everything held to `inner` now.
    flush &self -> void {
        if (self.pos > 0) {
            unsafe { self.inner.write(&self.data as long, self.pos); }
            self.pos = 0;
        }
    }
    // Change when this writer flushes. What is already held is passed on first, so nothing
    // written under the old mode waits on the new one's rule.
    setMode &self m:BufferMode -> void {
        self.flush();
        self.mode = m;
    }
}
methods BufWriter<W, N> {
    // Does the mode say what is held should go now?
    due &self -> bool {
        match self.mode {
            Block        { return false; }
            Unbuffered   { return true; }
            Line(c)      { return self.pos > 0 && self.data[self.pos - 1] == c as u8; }
            Delimited(d) {
                if (d.len == 0 || d.len > self.pos) { return false; }
                return bytesEqual(self.data[self.pos - d.len..self.pos], d as [u8]);
            }
        }
    }
    // Hold at most `n` bytes (1..N) before passing them on: a smaller window for a reader on the
    // other end of a pipe that should see output sooner than a full buffer. More than N takes a
    // writer whose type says more.
    setCapacity &self n:long -> void {
        c: long = n;
        if (c < 1) { c = 1; }
        if (c > N) { c = N; }
        self.cap = c;
    }
    // The most this writer can hold: N.
    capacity &self -> long { return N; }
}

// The buffer is part of the writer, so `inner` is moved into it. Line-buffered on '\n', which is
// what a terminal wants; `bufWriterWith` names the mode. N comes from where the result is stored
// (`b: BufWriter<File, 65536> = bufWriter(f);`), and is 4096 when nothing says.
pub bufWriter<W: Write, N: long = 4096> inner:W -> BufWriter<W, N> {
    return bufWriterWith(inner, BufferMode.Line('\n'));
}
pub bufWriterWith<W: Write, N: long = 4096> inner:W mode:BufferMode -> BufWriter<W, N> {
    return BufWriter { inner: inner, cap: N, pos: 0, mode: mode };
}

// ─── StringWriter: capture into a caller buffer ─────────────────────────────
// Formatting into memory the caller already has, with no allocation: read the result back
// through `.buf` / `.len`, or `view`. Fixed capacity — a write past `cap` is truncated, not grown.
// (`string.format` is the growing, allocating form.)
pub struct StringWriter { buf: *u8, cap: long, len: long }
methods StringWriter for Write {
    write &self ptr:long len:long -> long {
        n: long = len;
        if (n > self.cap - self.len) { n = self.cap - self.len; }
        unsafe { memcpy(self.buf + self.len, ptr, n); }   // *u8 arithmetic: byte-scaled
        self.len = self.len + n;
        return n;
    }
}
methods StringWriter for Default {
    new -> StringWriter { unsafe { return StringWriter { buf: 0 as *u8, cap: 0, len: 0 }; } }
}
methods StringWriter {
    // What has been written, as a view of the caller's buffer.
    unsafe view &self -> str { return self.buf[..self.len] as str; }
    // Start over at the beginning of the same buffer.
    reset &self -> void { self.len = 0; }
    // Did a write not fit?
    full &self -> bool { return self.len == self.cap; }
}
// `unsafe`: the writer outlives this call, so the caller vouches that `bufPtr` names `cap`
// live bytes for as long as it is used.
pub unsafe stringWriter bufPtr:long cap:long -> StringWriter {
    return StringWriter { buf: bufPtr as *u8, cap: cap, len: 0 };
}
