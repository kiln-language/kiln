// stdlib::hash128 against the reference MurmurHash3_x64_128 (seed 0), whose output these are,
// and streamed input against one-shot. Exits 0 when every check holds, otherwise the number of
// the first one that did not.
#include <stdlib::hash128>
#include <stdlib::string>
#include <stdlib::vec>

same text:str want:str -> bool {
    h: Hash128 = hash128Str(text);
    got: String = h.hex();
    return got == want;
}

main -> int {
    if (!same("", "00000000000000000000000000000000")) { return 1; }
    if (!same("a", "85555565f6597889e6b53a48510e895a")) { return 2; }
    if (!same("hello", "cbd8a7b341bd9b025b1e906a48ae1d19")) { return 3; }
    if (!same("The quick brown fox jumps over the lazy dog", "e34bbc7bbc071b6c7a433ca9c49a9347")) { return 4; }
    // Exactly one block, one block and a byte, and a block with a fifteen-byte tail.
    if (!same("0123456789abcdef", "4be06d94cf4ad1a787c35b5c63a708da")) { return 5; }
    if (!same("0123456789abcdefg", "8e32612daa45f9de0800f4c206c372ee")) { return 6; }
    if (!same("0123456789abcdef0123456789abcde", "9afbac977e4daf0089fe4cda7efd8251")) { return 7; }
    b: [u8; 1000];
    k: long = 0;
    while (k < 1000) { b[k] = (k * 7) as u8; k = k + 1; }
    whole: Hash128 = hash128(b[..]);
    hx: String = whole.hex();
    if (!(hx == "0dc15cd8f7246c776ad442de1cdd03d8")) { return 8; }
    // Any split of the same bytes is the same hash.
    s: Hasher128;
    s.update(b[0..3]); s.update(b[3..20]); s.update(b[20..21]); s.update(b[21..999]); s.update(b[999..]);
    if (!(s.finish() == whole)) { return 9; }
    return 0;
}
