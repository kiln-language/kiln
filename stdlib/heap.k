// Heap — a thread-cached segregated free-list allocator with an arena/slab fallback.
//
//   [ TLS thread cache ]   fast:   size class -> pop from per-thread free list  (O(1), no lock)
//        | empty
//   [ central arena pool ] medium: carve a fresh 64 KiB slab (CAS-bump, no global lock)
//        | exhausted
//   [ OS kernel (mmap) ]   slow:   map a new multi-MB segment                   (rare)
//
// heapInit() runs once at the top of each thread (main + spawned) before malloc: an `@init` hook
// for the main thread, and `thread.spawn` calls it for a child. In the compile-time evaluator,
// malloc, free and realloc are mmap, munmap and mremap: it has no thread page.
//
// The safe boundary of this file is malloc (fresh memory) + the Box/Rc/Arc/Raw types. Inside it,
// what a typed pointer can say is said with one: the central pool is a struct, a free slot's
// first word is its successor. `asm` is left only for fs-relative TLS access and naming the
// pool's symbol.
#include <{sys, mem, core, atomic, panic}>

// ─── layout ──────────────────────────────────────────────────────────────────
// Size classes: 16, 32, ..., 512 in 16-byte steps (classes 0..31), then four per doubling up to
// 8 KiB: 640, 768, 896, 1024, 1280, ..., 8192 (classes 32..47), so no class wastes more than a
// fifth of its slot. A slab is a 64 KiB, 64 KiB-aligned chunk for one class, so free() recovers
// the class by masking a pointer to the slab and reading its first word. Requests over 8 KiB get
// a region of their own with the same alignment, whose first word says so; a freed one is kept
// in a small cache for the next large request instead of going back to the kernel at once.
local SMALL_MAX:   long = 512;
local SLAB_MAX:    long = 8192;          // the largest slab class
local CLASSES:     long = 48;
local SLAB:        long = 65536;
local SLAB_MASK:   long = ~65535;
local SLAB_HEADER: long = 16;
local ARENA:       long = 16777216;      // one mmap of slabs at a time
local BATCH_BYTES: long = 32768;         // how much a batch moved between a thread and the pool holds

// The large-region cache: at most this many regions and bytes held for reuse, none bigger than
// CACHE_ONE. Past these, a freed region is unmapped as before.
local CACHE_COUNT: long = 32;
local CACHE_BYTES: long = 67108864;      // 64 MiB
local CACHE_ONE:   long = 16777216;      // 16 MiB
// A large block at least this big grows by mremap, moving its pages rather than copying them.
local REMAP_MIN:   long = 1048576;

// What the first word of a 64 KiB-aligned region says it is, beyond a size class (0..47).
local LARGE_REGION:  long = 999;
local STATIC_REGION: long = 1000;   // a block the compiler laid into .data (asm.k's emitBlocks)

// The pool every thread shares, at [rel __heapCentral] (1 KiB the emitter reserves; this uses
// 824 bytes of it). Per class a free-slot list head and a spinlock — so no lock is global — then
// the arena's bump pointer, its end, and the lock held while a fresh arena is mapped; then the
// large-region cache: its lock, its list (linked through the regions' headers), and its totals.
struct HeapCentral {
    heads: [long; CLASSES], locks: [long; CLASSES], bump: long, end: long, arenaLock: long,
    largeLock: long, cacheHead: long, cacheBytes: long, cacheCount: long
}

// The header of a large allocation, at its region's base; the payload starts 64 bytes in.
// `next` links a cached region to the next one.
struct LargeHeader { marker: long, base: long, size: long, next: long }
local LARGE_PAYLOAD: long = 64;

// Per thread, through fs: [cls*8] the free-list head, [TLS_COUNTS + cls*8] how many it holds.
// The page is the TLS page heapInit maps; nothing else uses it.
local TLS_COUNTS: long = CLASSES * 8;

// mmap(2)'s protection and flag bits, the ones this file passes.
enum MmapProt: long { Read = 1, Write = 2 }
enum MmapFlag: long { Private = 0x2, Anonymous = 0x20, NoReserve = 0x4000 }
enum ArchCode: long { SetFs = 0x1002 }
enum MremapFlag: long { MayMove = 1, Fixed = 2 }

// ─── primitives ──────────────────────────────────────────────────────────────

local unsafe central -> *HeapCentral {
    a: long = 0;
    asm { "lea rax, [rel __heapCentral]" out a rax; }
    return a as *HeapCentral;
}
// per-thread storage: fs points at this thread's TLS page; [fs:off] is thread-local.
local unsafe tlsLoad off:long -> long {
    v: long = 0;
    asm { in rdi off; "mov rax, [fs:rdi]" out v rax; }
    return v;
}
local unsafe tlsStore off:long v:long -> void {
    asm { in rdi off; in rsi v; "mov [fs:rdi], rsi" }
}
// A free slot's first word links to the next one; a region's first word is its marker.
local unsafe slotWord p:long -> *long { return p as *long; }

// An anonymous, private, lazily committed mapping. There is nothing to fall back on when the
// kernel refuses one, so that ends the program with a message rather than handing out address 0.
local unsafe mapAnon size:long flags:long -> long {
    p: long = syscall6(Syscall.Mmap, 0, size, MmapProt.Read | MmapProt.Write, MmapFlag.Private | MmapFlag.Anonymous | flags, -1, 0);
    if (p < 0) { panic("heap: the kernel refused memory (mmap failed)"); }
    return p;
}
local roundUpTo v:long to:long -> long { return (v + to - 1) & ~(to - 1); }

// Give the calling thread a fresh, zeroed TLS page and point fs at it. Must be called before
// any malloc/free on that thread.
@init heapInit -> void {
    unsafe {
        page: long = mapAnon(4096, 0);
        syscall2(Syscall.ArchPrctl, ArchCode.SetFs, page);
    }
}

// ─── allocator ───────────────────────────────────────────────────────────────

// 1..512 -> 0..31; 513..8192 -> 32..47 (the caller ensures n <= SLAB_MAX).
local sizeClass n:long -> long {
    if (n < 1) { return 0; }
    if (n <= SMALL_MAX) { return ((n + 15) >> 4) - 1; }
    lg: long = 9;                           // floor(log2(n - 1)): n - 1 is at least 512
    while (((n - 1) >> (lg + 1)) != 0) { lg = lg + 1; }
    return 32 + (lg - 9) * 4 + ((n - 1) >> (lg - 2)) - 4;
}
// The bytes a class's slot holds.
local classSize cls:long -> long {
    if (cls < 32) { return (cls + 1) * 16; }
    base: long = SMALL_MAX << ((cls - 32) / 4);
    return base + ((cls - 32) % 4 + 1) * (base / 4);
}
// How many slots move between a thread and the pool at once: about 32 KiB of them, 4 to 64.
// (Every free asks, so the 32 small classes, all 64, answer before any division.)
local batchOf cls:long -> long {
    if (cls < 32) { return 64; }
    b: long = BATCH_BYTES / classSize(cls);
    if (b > 64) { return 64; }
    if (b < 4) { return 4; }
    return b;
}

// --- per-thread free list (fast path, no lock) ---
// Each is one asm block rather than a call per thread-local word: this is the path every small
// malloc and free takes. No labels (an inlined copy would repeat them), inputs in rdi/rsi only,
// and no size keywords (a count is loaded, changed and stored through a register), so the same
// text assembles under NASM and under LLVM (`--emit=llvm`). The count of class `cls` sits
// TLS_COUNTS (384) bytes after its head; the asm spells the number.
local unsafe tlsPop cls:long -> long {
    off: long = cls * 8;
    h: long = tlsLoad(off);
    if (h == 0) { return 0; }
    asm {
        in rdi off;
        in rsi h;
        "mov rdx, [rsi]"                    // head = head.next
        "mov [fs:rdi], rdx"
        "mov rdx, [fs:rdi + 384]"
        "dec rdx"
        "mov [fs:rdi + 384], rdx"
    }
    return h;
}
// Push `p`; answers how many slots the list now holds.
local unsafe tlsPush cls:long p:long -> long {
    off: long = cls * 8;
    n: long = 0;
    asm {
        in rdi off;
        in rsi p;
        "mov rdx, [fs:rdi]"                 // p.next = head; head = p
        "mov [rsi], rdx"
        "mov [fs:rdi], rsi"
        "mov rax, [fs:rdi + 384]"
        "inc rax"
        "mov [fs:rdi + 384], rax"
        out n rax;
    }
    return n;
}

// --- central shared free-slot pool (per-class lock => no global lock; medium path) ---
local unsafe centralLock cls:long -> void {
    c: *HeapCentral = central();
    l: *long = &c.locks[cls] as *long;
    loop { if (atomicCas(l, 0, 1) == 0) { return; } }
}
local unsafe centralUnlock cls:long -> void {
    c: *HeapCentral = central();
    atomicStore(&c.locks[cls] as *long, 0);
}

// --- arena: hand out 64 KiB slabs. The bump only increases, so its CAS is ABA-free. ---
local unsafe extendArena -> void {
    c: *HeapCentral = central();
    l: *long = &c.arenaLock as *long;
    if (atomicCas(l, 0, 1) != 0) {
        while (atomicLoad(l) != 0) { }               // another thread is mapping: wait for it
        return;
    }
    if (c.bump == 0 || c.bump + SLAB > c.end) {      // none yet, or exhausted: a fresh segment
        base: long = mapAnon(ARENA, MmapFlag.NoReserve);
        c.end = base + ARENA;
        c.bump = roundUpTo(base, SLAB);
    }
    atomicStore(l, 0);
}
local unsafe grabSlab -> long {
    c: *HeapCentral = central();
    loop {
        bump: long = c.bump;
        if (bump == 0 || bump + SLAB > c.end) { extendArena(); }
        else if (atomicCas(&c.bump as *long, bump, bump + SLAB) == bump) { return bump; }
    }
}
// Pull a batch of slots from the central pool into this thread's free list. If the central pool
// for `cls` is empty, carve a fresh slab into it first. This keeps the TLS cache small so
// malloc/free stay on the lock-free fast path most of the time.
local unsafe tlsRefill cls:long -> void {
    c: *HeapCentral = central();
    centralLock(cls);
    if (c.heads[cls] == 0) {
        slab: long = grabSlab();
        *slotWord(slab) = cls;
        size: long = classSize(cls);
        slots: long = (SLAB - SLAB_HEADER) / size;
        for i in 0..slots {
            p: long = slab + SLAB_HEADER + i * size;
            *slotWord(p) = c.heads[cls];
            c.heads[cls] = p;
        }
    }
    for k in 0..batchOf(cls) {
        h: long = c.heads[cls];
        if (h == 0) { break; }
        c.heads[cls] = *slotWord(h);
        tlsPush(cls, h);
    }
    centralUnlock(cls);
}
// Return a batch of surplus slots from the TLS cache to the central pool.
local unsafe tlsSpill cls:long -> void {
    c: *HeapCentral = central();
    centralLock(cls);
    for k in 0..batchOf(cls) {
        s: long = tlsPop(cls);
        if (s == 0) { break; }
        *slotWord(s) = c.heads[cls];
        c.heads[cls] = s;
    }
    centralUnlock(cls);
}

// --- large allocations (> 8 KiB): a dedicated, 64 KiB-aligned mmap, cached when freed ---
local unsafe largeLock -> void {
    l: *long = &central().largeLock as *long;
    loop { if (atomicCas(l, 0, 1) == 0) { return; } }
}
local unsafe largeUnlock -> void { atomicStore(&central().largeLock as *long, 0); }

// The bytes a large region holds from `p` to its end.
local unsafe largeRoom p:long -> long {
    h: *LargeHeader = (p & SLAB_MASK) as *LargeHeader;
    return h.base + h.size - p;
}
local unsafe largeAlloc n:long -> long {
    size: long = roundUpTo(n + LARGE_PAYLOAD + SLAB, 4096);      // header + payload + alignment slack
    // A cached region that fits and is not more than twice what is asked: the smallest such.
    c: *HeapCentral = central();
    largeLock();
    best: long = 0;
    bestSize: long = 0;
    bestPrev: long = 0;
    prev: long = 0;
    at: long = c.cacheHead;
    while (at != 0) {
        r: *LargeHeader = at as *LargeHeader;
        if (r.size >= size && r.size <= size * 2 && (best == 0 || r.size < bestSize)) {
            best = at;
            bestSize = r.size;
            bestPrev = prev;
        }
        prev = at;
        at = r.next;
    }
    if (best != 0) {
        b: *LargeHeader = best as *LargeHeader;
        if (bestPrev == 0) { c.cacheHead = b.next; }
        else { bp: *LargeHeader = bestPrev as *LargeHeader; bp.next = b.next; }
        c.cacheBytes = c.cacheBytes - b.size;
        c.cacheCount = c.cacheCount - 1;
        largeUnlock();
        return best + LARGE_PAYLOAD;
    }
    largeUnlock();
    base: long = mapAnon(size, MmapFlag.NoReserve);
    h: *LargeHeader = roundUpTo(base, SLAB) as *LargeHeader;
    h.marker = LARGE_REGION;
    h.base = base;
    h.size = size;
    return h as long + LARGE_PAYLOAD;
}
// Kept for the next large request while the cache has room; unmapped otherwise.
local unsafe largeFree p:long -> void {
    h: *LargeHeader = (p & SLAB_MASK) as *LargeHeader;
    c: *HeapCentral = central();
    if (h.size <= CACHE_ONE) {
        largeLock();
        if (c.cacheCount < CACHE_COUNT && c.cacheBytes + h.size <= CACHE_BYTES) {
            h.next = c.cacheHead;
            c.cacheHead = h as long;
            c.cacheBytes = c.cacheBytes + h.size;
            c.cacheCount = c.cacheCount + 1;
            largeUnlock();
            return;
        }
        largeUnlock();
    }
    syscall2(Syscall.Munmap, h.base, h.size);
}
// Grow a large region to hold `n` bytes from its payload by moving its pages with mremap: a
// fresh reservation is mapped, the region moved into it where its header lands 64 KiB-aligned,
// and what is left of the reservation unmapped. No byte is copied.
local unsafe largeRemap p:long n:long -> long {
    h: *LargeHeader = (p & SLAB_MASK) as *LargeHeader;
    off: long = h as long - h.base;                    // where the header sits in the region
    size: long = roundUpTo(off + LARGE_PAYLOAD + n, 4096);
    resv: long = mapAnon(size + SLAB, MmapFlag.NoReserve);
    at: long = roundUpTo(resv + off, SLAB) - off;      // at >= resv, and the header lands aligned
    r: long = syscall6(Syscall.Mremap, h.base, h.size, size, MremapFlag.MayMove | MremapFlag.Fixed, at, 0);
    if (r != at) { panic("heap: the kernel refused to move memory (mremap failed)"); }
    if (at > resv) { syscall2(Syscall.Munmap, resv, at - resv); }
    tail: long = resv + size + SLAB - (at + size);
    if (tail > 0) { syscall2(Syscall.Munmap, at + size, tail); }
    nh: *LargeHeader = (at + off) as *LargeHeader;
    nh.base = at;
    nh.size = size;
    return at + off + LARGE_PAYLOAD;
}

// Allocate n bytes — any size. Up to 8 KiB: lock-free TLS pop (refilled in batches from the
// shared pool); larger: a region of its own, from the cache when one fits.
pub malloc n:long -> long {
    unsafe {
        if (atCompileTime()) { return syscall(Syscall.Mmap as long, 0, n, 3, 0x22, -1, 0); }
        if (n > SLAB_MAX) { return largeAlloc(n); }
        cls: long = sizeClass(n);
        p: long = tlsPop(cls);                      // fast: this thread's cache (no lock)
        if (p == 0) {
            tlsRefill(cls);                         // batch from central (carving a slab if needed)
            p = tlsPop(cls);
        }
        return p;
    }
}

// Free a block. Slab blocks go to the lock-free thread cache; once it holds four batches, one
// goes back to the shared pool (cross-thread reuse). Large regions go to the large cache, or back
// to the OS, and a block the compiler laid into the binary is never ours to release. Freeing 0 is
// a no-op, as in C. `unsafe`: freeing a bad/live/foreign address corrupts the heap — the caller
// must vouch that p came from malloc and is done for good.
pub unsafe free p:long -> void {
    if (p == 0) { return; }
    if (atCompileTime()) { syscall(Syscall.Munmap as long, p, 1); return; }
    marker: long = *slotWord(p & SLAB_MASK);
    if (marker == STATIC_REGION) { return; }
    if (marker == LARGE_REGION) { largeFree(p); return; }
    if (tlsPush(marker, p) > 4 * batchOf(marker)) { tlsSpill(marker); }     // fast: thread-local
}

// The block `p` (with its first `old` bytes worth keeping) made to hold `n`: in place when it
// already has the room, by mremap when it is a large region of 1 MiB or more, otherwise a fresh
// block with the `old` bytes copied over. `p` is 0 for a first allocation. `unsafe` as free is:
// when the block moves, `p` is released and must not be used again.
pub unsafe realloc p:long old:long n:long -> long {
    if (p == 0) { return malloc(n); }
    if (atCompileTime()) { return syscall(Syscall.Mremap as long, p, old, n, 1, 0); }
    marker: long = *slotWord(p & SLAB_MASK);
    if (marker < CLASSES && n <= classSize(marker)) { return p; }
    if (marker == LARGE_REGION) {
        room: long = largeRoom(p);
        if (n <= room) { return p; }
        if (room >= REMAP_MIN) { return largeRemap(p, n); }
    }
    return moveBlock(p, old, n);
}
local unsafe moveBlock p:long old:long n:long -> long {
    q: long = malloc(n);
    keep: long = old;
    if (keep > n) { keep = n; }
    if (keep > 0) { memcpy(q, p, keep); }
    free(p);
    return q;
}

// Release the value at `p` (run its drop glue, if it has any), leaving the memory to the caller.
// A load through a raw pointer is a move out of it, and the local it lands in is released at
// the closing brace: that is how generic code runs a `T`'s drop.
local unsafe dropInPlace<T> p:*T -> void {
    gone: T = *p;
}

// ─── Box<T>: a heap-owned value ──────────────────────────────────────────────
// A typed handle to a heap allocation holding one T. `newBox(v)` allocates and moves v in; the
// value is read in place with `at`, copied with `get`/`set` when T is Copy, and released — the
// value, then the block — when the Box is.
pub struct Box<T> { ptr: *T }

pub newBox<T> v:T -> Box<T> {
    unsafe {
        p: *T = malloc(sizeof(T)) as *T;
        *p = v;                                  // one typed store, whatever T's width
        return Box { ptr: p };
    }
}

// get/set bitwise-copy the value in/out, so they exist only for Copy contents — copying a Drop
// value out would double-release its resource on the second drop.
methods Box<T: Copy> {
    get &self -> T { unsafe { return *self.ptr; } }
    set &self v:T -> void { unsafe { *self.ptr = v; } }
}
// A borrow of the contents, whatever T is — the same borrow `Vec.at` hands out, and for the
// same reason: an owning value is read in place rather than copied out. It is what makes a
// `Box<Tree>` inside `Tree` walkable at all; `get` needs Copy, and a tree owns its subtrees.
methods Box<T> {
    at &self -> &T { unsafe { return *self.ptr; } }
}
// The value, then the block.
methods Box<T> for Drop {
    drop &self -> void {
        unsafe {
            if (self.ptr as long == 0) { return; }
            dropInPlace(self.ptr);
            free(self.ptr);
        }
    }
}
methods Box<T: Clone> for Clone {
    // Deep copy: a fresh allocation holding a clone of the value.
    clone &self -> Box<T> { return newBox(self.at().clone()); }
}

// ─── Raw: a manual, untyped heap block ───────────────────────────────────────
// Every access is an offset into the `len`-byte block and is BOUNDS-CHECKED (out of range is a
// panic naming the access, like a slice index) — that's what makes loadAt/storeAt genuinely
// safe. The block is released when the Raw is dropped; `free` releases it early and leaves an
// empty Raw behind, so a dropped Raw that was freed releases nothing twice. `address()` stays
// `unsafe`: it leaks the raw pointer, which outlives nothing the checker can see.
pub struct Raw { ptr: *u8, len: long }

methods Raw {
    // Allocate an n-byte block:  m: Raw = Raw.new(64);
    new n:long -> Raw {
        unsafe { return Raw { ptr: malloc(n) as *u8, len: n }; }
    }
    // `width` bytes at `off` must lie inside the block.
    check &self what:str off:long width:long -> void {
        if (off < 0 || off + width > self.len) { panicIndex(what, off, self.len); }
    }
    // Read/write an 8-byte word at a byte offset.
    loadAt &self off:long -> long {
        self.check("Raw.loadAt", off, 8);
        unsafe { return *((self.ptr + off) as *long); }
    }
    storeAt &self off:long v:long -> void {
        self.check("Raw.storeAt", off, 8);
        unsafe { *((self.ptr + off) as *long) = v; }
    }
    // Read/write a single byte at an offset — same bounds check, byte granularity.
    loadByteAt &self off:long -> u8 {
        self.check("Raw.loadByteAt", off, 1);
        unsafe { return self.ptr[off]; }
    }
    storeByteAt &self off:long v:u8 -> void {
        self.check("Raw.storeByteAt", off, 1);
        unsafe { self.ptr[off] = v; }
    }
    // Fill the whole block with one byte value.
    fill &self v:u8 -> void { unsafe { memset(self.ptr, v as long, self.len); } }
    // The raw base address (for interop, e.g. handing a buffer to a syscall).
    unsafe address &self -> long { return self.ptr; }
    size &self -> long { return self.len; }
    // Release the block now. What is left is an empty Raw: every access to it is out of range.
    free &self -> void {
        unsafe { free(self.ptr); }
        self.ptr = 0 as *u8;
        self.len = 0;
    }
}
methods Raw for Drop {
    drop &self -> void { self.free(); }
}

// ─── Rc<T> and Arc<T>: a reference-counted heap value ────────────────────────
// The block is one allocation, [ count:long | value:T ]: `*u8` is its honest type, since the two
// halves have different types; the count is reached through a `*long` at offset 0 and the value
// through a `*T` at offset 8 (8-aligned, so T's alignment is satisfied). clone() bumps the count;
// drop() lowers it, and the last handle releases the value and the block.
//
// Rc counts with plain arithmetic and stays on one thread; Arc counts with lock-prefixed atomics,
// so handles can be cloned and dropped from different threads. Share an Arc across a spawn() by
// handing the pointer over; each thread drops its own handle.
local unsafe newCounted<T> v:T -> *u8 {
    p: *u8 = malloc(8 + sizeof(T)) as *u8;
    c: *long = p as *long;
    *c = 1;                                      // no other handle exists yet
    val: *T = (p + 8) as *T;
    *val = v;
    return p;
}
// Given the value's address, which is what carries `T`: the block starts 8 bytes before it.
local unsafe releaseCounted<T> val:*T -> void {
    dropInPlace(val);
    free(val as long - 8);
}

pub struct Rc<T> { ptr: *u8 }

pub newRc<T> v:T -> Rc<T> { unsafe { return Rc { ptr: newCounted(v) }; } }

methods Rc<T> {
    unsafe countPtr &self -> *long { return self.ptr as *long; }
    unsafe valuePtr &self -> *T    { return (self.ptr + 8) as *T; }
    count &self -> long { unsafe { return *self.countPtr(); } }
    // A borrow of the shared value, in place. Single-threaded, so nothing else is reading it
    // while the borrow lasts — the same footing `Box.at` stands on.
    at &self -> &T { unsafe { p: *T = self.valuePtr(); return *p; } }
}
methods Rc<T: Copy> {
    // Copy-out is Copy-only (a Drop value would double-release).
    get &self -> T { unsafe { p: *T = self.valuePtr(); return *p; } }
}
methods Rc<T> for Clone {
    // Share ownership: bump the count, hand back another handle to the same block.
    clone &self -> Rc<T> {
        unsafe { c: *long = self.countPtr(); *c = *c + 1; }
        return Rc { ptr: self.ptr };
    }
}
methods Rc<T> for Drop {
    drop &self -> void {
        unsafe {
            c: *long = self.countPtr();
            *c = *c - 1;
            if (*c == 0) { releaseCounted(self.valuePtr()); }
        }
    }
}

pub struct Arc<T> { ptr: *u8 }

pub newArc<T> v:T -> Arc<T> { unsafe { return Arc { ptr: newCounted(v) }; } }

methods Arc<T: Copy> {
    // Copy-out is Copy-only (a Drop value would double-release).
    get &self -> T { unsafe { p: *T = (self.ptr + 8) as *T; return *p; } }
}
methods Arc<T> {
    // A plain aligned load: the count is only ever mutated through lock-prefixed
    // read-modify-writes, and an aligned 8-byte read is atomic on x86-64.
    count &self -> long { unsafe { return atomicLoad(self.ptr as *long); } }
}
methods Arc<T> for Clone {
    clone &self -> Arc<T> {
        unsafe { atomicAdd(self.ptr as *long, 1); }
        return Arc { ptr: self.ptr };
    }
}
methods Arc<T> for Drop {
    drop &self -> void {
        unsafe {
            if (atomicSub(self.ptr as *long, 1) == 1) { releaseCounted((self.ptr + 8) as *T); }   // we took it to zero
        }
    }
}
