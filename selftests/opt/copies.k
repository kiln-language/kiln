// `memcpy` writes its destination range and nothing else. A borrowed struct's own fields read
// before a copy into the buffer it points at are still known after it, while a word read from
// the destination is read again. The copy is written where it is, and its lengths being constants,
// as moves rather than `rep movsb` (`emitShortCopy`).
// ir-count: copies::append ptrload 2
// ir-count: copies::append memcopy 1
// ir-count: copies::reread ptrload 2
// asm-lacks: main rep movsb
// asm-lacks: main mfn_copies$append
pub unsafe builtin memcpy dst:long src:long n:long -> void;

struct Buf { ptr: long, len: long, cap: long }

append b:&Buf src:long n:long -> long {
    at: long = b.len;
    unsafe { memcpy(b.ptr + at, src, n); }
    return b.len + at;
}
unsafe reread p:*long src:long -> long {
    a: long = p[0];
    memcpy(p as long, src, 8);
    return p[0] + a;
}
main -> long {
    data: [long; 4];
    out: [long; 8];
    for i in 0..4 { data[i] = i + 1; }
    for i in 0..8 { out[i] = 0; }
    b: Buf;
    unsafe { b = Buf { ptr: &out as long, len: 8, cap: 64 }; }
    r: long = 0;
    unsafe { r = append(&b, &data as long, 16); }
    if (r != 16 || out[1] != 1 || out[2] != 2) { return 1; }
    unsafe { r = reread(&out as *long, &data as long + 16); }
    if (r != 3) { return 2; }
    return 0;
}
