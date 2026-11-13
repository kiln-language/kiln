// Random numbers. `fillRandom`/`randomU64` ask the kernel (getrandom): unpredictable, for seeds,
// keys and unique names. `Rng` is a fast seedable generator (xoshiro256**) for everything else:
// simulations, shuffles, tests that must repeat with `Rng.seeded(n)`.
#include <{core, sys, result, vec}>

local SM_GAMMA: u64 = 0x9E3779B97F4A7C15;
local SM_MUL1: u64 = 0xBF58476D1CE4E5B9;
local SM_MUL2: u64 = 0x94D049BB133111EB;

// Fill `buf` from the kernel's generator. Ok(len), or Err(errno).
pub fillRandom inout buf:[u8] -> Result<long, long> {
    got: long = 0;
    while (got < buf.len) {
        n: long = 0;
        unsafe { n = syscall3(Syscall.Getrandom, buf.ptr + got, buf.len - got, 0); }
        if (n == -Errno.Intr) { continue; }
        if (n < 0) { return Result.Err(-n); }
        got = got + n;
    }
    return Result.Ok(got);
}

pub randomU64 -> u64 {
    b: [u8; 8];
    r: Result<long, long> = fillRandom(&b[..]);
    v: u64 = 0;
    for k in 0..8 { v = (v << 8) | (b[k] as u64); }
    return v;
}

pub struct Rng { s0: u64, s1: u64, s2: u64, s3: u64 }

local rotl x:u64 k:long -> u64 { return (x << k) | (x >> (64 - k)); }

methods Rng {
    // The same seed gives the same sequence, on every run.
    seeded seed:u64 -> Rng {
        r: Rng = Rng { s0: 0, s1: 0, s2: 0, s3: 0 };
        x: u64 = seed;
        x = x + SM_GAMMA; r.s0 = splitmix(x);
        x = x + SM_GAMMA; r.s1 = splitmix(x);
        x = x + SM_GAMMA; r.s2 = splitmix(x);
        x = x + SM_GAMMA; r.s3 = splitmix(x);
        return r;
    }
    fromEntropy -> Rng { return Rng.seeded(randomU64()); }

    next &self -> u64 {
        out: u64 = rotl(self.s1 * 5, 7) * 9;
        t: u64 = self.s1 << 17;
        self.s2 = self.s2 ^ self.s0;
        self.s3 = self.s3 ^ self.s1;
        self.s1 = self.s1 ^ self.s2;
        self.s0 = self.s0 ^ self.s3;
        self.s2 = self.s2 ^ t;
        self.s3 = rotl(self.s3, 45);
        return out;
    }
    // Uniform in 0..n (n > 0): rejection, so every value is equally likely.
    below &self n:long -> long {
        bound: u64 = n as u64;
        limit: u64 = ((0 as u64) - bound) % bound;   // 2^64 mod n: the biased low end to skip
        loop {
            v: u64 = self.next();
            if (v >= limit) { return (v % bound) as long; }
        }
        return 0;
    }
    // Uniform in lo..hi (half-open, lo < hi).
    range &self lo:long hi:long -> long { return lo + self.below(hi - lo); }
    // A coin that comes up true with probability num/den.
    chance &self num:long den:long -> bool { return self.below(den) < num; }
}

local splitmix x:u64 -> u64 {
    z: u64 = x;
    z = (z ^ (z >> 30)) * SM_MUL1;
    z = (z ^ (z >> 27)) * SM_MUL2;
    return z ^ (z >> 31);
}

// Fisher-Yates: every order equally likely.
pub shuffle<T> inout v:Vec<T> inout r:Rng -> void {
    i: long = v.len() - 1;
    while (i > 0) {
        j: long = r.below(i + 1);
        v.swap(i, j);
        i = i - 1;
    }
}
