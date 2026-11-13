// A length as a template parameter: `struct Ring<T, N: long>` holds `[T; N]` inline, and its
// methods read N as a `long`. Each length is its own instance, laid out at its own size, with
// its own bounds; two spellings of one length (`8` and a constant equal to it) are one instance;
// a length only a return type names comes from the destination; one the call cannot see takes
// the declared default; a type parameter may have a default too. Exit 0 when every check holds,
// otherwise the number of the first that did not.
#include <stdlib::vec>

EIGHT: long = 4 * 2;
pub WIDE: long = EIGHT * 512;               // a constant built from another

struct Ring<T, N: long> { data: [T; N], head: long, len: long }

methods Ring<T: Copy, N> {
    cap &self -> long { return N; }
    push &self v:T -> bool {
        if (self.len == N) { return false; }
        self.data[(self.head + self.len) % N] = v;
        self.len = self.len + 1;
        return true;
    }
    pop &self -> T {
        v: T = self.data[self.head];
        self.head = (self.head + 1) % N;
        self.len = self.len - 1;
        return v;
    }
    // The whole array as a slice: its length is this instance's N.
    viewLen &self -> long { return self.data[..].len; }
    // A local array sized by the parameter, and `Ring<T>` inside its own methods meaning this
    // instance: `Ring<T, N>`.
    copied &self -> Ring<T> {
        tmp: [T; N];
        i: long = 0;
        while (i < N) { tmp[i] = self.data[i]; i = i + 1; }
        r: Ring<T> = Ring { head: self.head, len: self.len };
        i = 0;
        while (i < N) { r.data[i] = tmp[i]; i = i + 1; }
        return r;
    }
}

// N only in the return type: the destination says what it is.
ringOf<T: Copy, N: long> first:T -> Ring<T, N> {
    r: Ring<T, N> = Ring { head: 0, len: 0 };
    r.push(first);
    return r;
}

// N from the argument's own instance.
capOf<T: Copy, N: long> r:Ring<T, N> -> long { return r.cap() * 10 + N; }

// Defaults: a length, and a type.
struct Buf<T = u8, N: long = 16> { bytes: [T; N], used: long }
bufOf<N: long = 32> -> Buf<u8, N> { return Buf { used: N }; }

main -> int {
    r: Ring<long, 4> = Ring { head: 0, len: 0 };
    if (r.cap() != 4 || r.viewLen() != 4) { return 1; }
    for i in 0..6 { r.push(i * 10); }
    if (r.len != 4 || r.pop() != 0 || r.pop() != 10) { return 2; }
    r.push(77);
    if (r.pop() != 20 || r.pop() != 30 || r.pop() != 77) { return 3; }

    // Two spellings, one instance: this assignment type-checks only because they are one type.
    a: Ring<long, 8> = ringOf(5 as long);
    b: Ring<long, EIGHT> = a;
    if (b.cap() != 8 || b.pop() != 5) { return 4; }
    if (sizeof(Ring<long, 8>) != 8 * 8 + 16 || sizeof(Ring<u8, WIDE>) != 4096 + 16) { return 5; }

    // Inferred from the argument.
    if (capOf(r) != 44 || capOf(b) != 88) { return 6; }

    // A copy made through a local `[T; N]`.
    c: Ring<long, 4> = r.copied();
    c.push(1);
    if (c.len != r.len + 1 || c.cap() != 4) { return 7; }

    // Defaults: `Buf` is `Buf<u8, 16>`, and `bufOf()` is `bufOf<32>` unless the destination says.
    d: Buf = Buf { used: 0 };
    if (sizeof(Buf) != 16 + 8 || d.bytes[..].len != 16) { return 8; }
    e: Buf<u8, 32> = bufOf();
    f: Buf<u8, 64> = bufOf();
    if (e.used != 32 || f.used != 64 || f.bytes[..].len != 64) { return 9; }
    g: Buf<long> = Buf { used: 3 };
    if (sizeof(Buf<long>) != 16 * 8 + 8 || g.bytes[..].len != 16) { return 10; }

    // An array sized by a constant expression.
    raw: [u8; EIGHT + 1];
    if (raw[..].len != 9) { return 11; }
    return 0;
}
