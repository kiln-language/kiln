// A local array declared without a value is zero in every byte, not only in its whole words:
// [u8; 13] and [u8; 20] end in a tail narrower than a word (dword, word, byte stores after the
// unrolled quadwords), [u8; 300] in one after `rep stosq`. A frame is dirtied first, so what the
// fill misses shows.
dirty -> long {
    junk: [long; 64];
    i: long = 0;
    while (i < 64) { junk[i] = 0x4142434445464748; i = i + 1; }
    return junk[3];
}
put inout out:[u8] -> long { out[0] = 120; return 1; }
nz13 -> long { d: [u8; 13]; n: long = put(&d[..]); bad: long = 0; for i in n..13 { if (d[i] != 0) { bad = bad + 1; } } return bad; }
nz20 -> long { d: [u8; 20]; n: long = put(&d[..]); bad: long = 0; for i in n..20 { if (d[i] != 0) { bad = bad + 1; } } return bad; }
nz7 -> long { d: [u8; 7]; n: long = put(&d[..]); bad: long = 0; for i in n..7 { if (d[i] != 0) { bad = bad + 1; } } return bad; }
nz300 -> long { d: [u8; 301]; n: long = put(&d[..]); bad: long = 0; for i in n..301 { if (d[i] != 0) { bad = bad + 1; } } return bad; }
main -> long {
    r: long = 0;
    dirty(); r = r + nz13();
    dirty(); r = r + nz20() * 2;
    dirty(); r = r + nz7() * 4;
    dirty(); r = r + nz300() * 8;
    return r + 42;
}
