// A 128-bit content hash: MurmurHash3, the x64_128 variant, streamed.
//
//     h: Hasher128;
//     h.updateStr("manifest");
//     h.update(bytes);
//     key: Hash128 = h.finish();
//     println("{}", key.hex());          // 32 hex digits
//
// For identifying content, such as a build cache key or a file fingerprint. It is not a
// cryptographic hash, so do not rely on it against someone who controls the input. It is well
// distributed across all 128 bits and passes SMHasher. It is fast over whole files: two 64-bit
// lanes, one multiply-rotate-multiply per word, and no table. It also has published reference
// output, so this implementation is tested against the original and not just against itself.
//
// One call and any split of the same bytes across `update` calls give the same hash: the block
// loop carries a 16-byte tail between calls, and only `finish` mixes in the length.
#include <{core, string, cmp}>

// The two lanes' multipliers and the finalizer's, as the reference spells them in hex. Written
// as their signed twins and cast once, because a literal past 2^63 is refused even for a `u64`
// (STDLIB_REVIEW.md); the bits are the same.
local C1: u64 = 0x87C37B91114253D5;
local C2: u64 = 0x4CF5AD432745937F;
local F1: u64 = 0xFF51AFD7ED558CCD;
local F2: u64 = 0xC4CEB9FE1A85EC53;

// Each lane's word scrambled before it is folded in; the same in a block and in the tail.
local mixK1 k:u64 -> u64 { return rotl64(k * C1, 31) * C2; }
local mixK2 k:u64 -> u64 { return rotl64(k * C2, 33) * C1; }

pub struct Hash128 { lo: u64, hi: u64 }

methods Hash128 {
    // 32 lowercase hex digits: the first lane, then the second, each most significant digit
    // first. The spelling a key is written down and compared in.
    hex &self -> String {
        out: String;
        out.reserve(32);
        pushHex64(&out, self.lo);
        pushHex64(&out, self.hi);
        return out;
    }
}

methods Hash128 for Eq<Hash128> {
    eq &self other:Hash128 -> bool { return self.lo == other.lo && self.hi == other.hi; }
}
// `{}` prints the 32 hex digits `hex` builds.
methods Hash128 for Display {
    display &self w:Write -> void { s: String = self.hex(); writeTo(w, "{}", s); }
}
// A content hash is already well mixed, so as a table key its first lane is the bucket hash.
methods Hash128 for Hash {
    hash &self -> u64 { return self.lo; }
}

pub struct Hasher128 {
    h1: u64, h2: u64,
    tail: [u8; 16],     // bytes not yet making a whole block
    tailLen: long,
    total: long         // every byte seen, which the finalizer mixes in
}

methods Hasher128 for Default {
    new -> Hasher128 { return seeded128(0); }
}

// A hasher whose two lanes start at `seed` (the reference's seed parameter).
pub seeded128 seed:long -> Hasher128 {
    h: Hasher128 = Hasher128 { h1: seed as u64, h2: seed as u64, tailLen: 0, total: 0 };
    return h;
}

methods Hasher128 {
    update &self b:[u8] -> void {
        i: long = 0;
        n: long = b.len;
        self.total += n;
        // Top up a carried partial block first.
        if (self.tailLen > 0) {
            while (self.tailLen < 16 && i < n) {
                self.tail[self.tailLen] = b[i];
                self.tailLen += 1;
                i += 1;
            }
            if (self.tailLen < 16) { return; }
            unsafe {
                p: long = (&self.tail) as long;
                self.block(*(p as *u64), *((p + 8) as *u64));
            }
            self.tailLen = 0;
        }
        // Whole blocks straight out of the caller's bytes: two little-endian words each.
        unsafe {
            base: long = b.ptr as long;
            while (i + 16 <= n) {
                self.block(*((base + i) as *u64), *((base + i + 8) as *u64));
                i += 16;
            }
        }
        while (i < n) {
            self.tail[self.tailLen] = b[i];
            self.tailLen += 1;
            i += 1;
        }
    }

    updateStr &self s:str -> void { self.update(s as [u8]); }

    // One 16-byte block into both lanes.
    block &self k1in:u64 k2in:u64 -> void {
        h1: u64 = self.h1 ^ mixK1(k1in);
        h1 = (rotl64(h1, 27) + self.h2) * 5 + 1390208809;                 // 0x52dce729
        h2: u64 = self.h2 ^ mixK2(k2in);
        h2 = (rotl64(h2, 31) + h1) * 5 + 944331445;                       // 0x38495ab5
        self.h1 = h1;
        self.h2 = h2;
    }

    // The hash of everything given so far. The hasher itself is left as it was, so more may
    // still be added and asked for again.
    finish &self -> Hash128 {
        h1: u64 = self.h1;
        h2: u64 = self.h2;
        k1: u64 = 0;
        k2: u64 = 0;
        n: long = self.tailLen;
        // The reference's fall-through switch over the tail, written as two loops: bytes 8..15
        // into the second lane's word, 0..7 into the first's, each little-endian.
        j: long = n;
        while (j > 8) {
            j -= 1;
            k2 ^= ((self.tail[j] as u64) << ((j - 8) * 8));
        }
        if (n > 8) { h2 = h2 ^ mixK2(k2); }
        j = n;
        if (j > 8) { j = 8; }
        while (j > 0) {
            j -= 1;
            k1 ^= ((self.tail[j] as u64) << (j * 8));
        }
        if (n > 0) { h1 = h1 ^ mixK1(k1); }
        h1 ^= (self.total as u64);
        h2 ^= (self.total as u64);
        h1 += h2;
        h2 += h1;
        h1 = fmix64(h1);
        h2 = fmix64(h2);
        h1 += h2;
        h2 += h1;
        return Hash128 { lo: h1, hi: h2 };
    }
}

// The whole of `b` at once.
pub hash128 b:[u8] -> Hash128 {
    h: Hasher128;
    h.update(b);
    return h.finish();
}

pub hash128Str s:str -> Hash128 { return hash128(s as [u8]); }

local rotl64 x:u64 r:long -> u64 { return (x << r) | (x >> (64 - r)); }

// The finalizer: every input bit reaches every output bit.
local fmix64 k0:u64 -> u64 {
    k: u64 = k0;
    k ^= (k >> 33);
    k *= F1;
    k ^= (k >> 33);
    k *= F2;
    k ^= (k >> 33);
    return k;
}

local pushHex64 inout out:String v:u64 -> void {
    shift: long = 60;
    while (shift >= 0) {
        d: long = ((v >> shift) & 15) as long;
        if (d < 10) { out.push(('0' + d) as char); } else { out.push(('a' + d - 10) as char); }
        shift -= 4;
    }
}
