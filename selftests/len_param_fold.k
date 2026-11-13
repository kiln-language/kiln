// Length-generic instances at compile time. An immutable global is built by a generic function
// whose N comes only from the destination, its loop bound read at compile time and the result
// folded into `.rodata`; a `var` global shaped the way `io.k` builds stdout (a `Mutex` around an
// inline-buffered writer, given as literals) is folded into `.data`; a default length applies to
// a global's type; and a derive macro reads the per-instance length of an array field from its
// `reflect` view. Exit 0 when every check holds, otherwise the number of the first that did not.
#include <stdlib::ast>
#include <stdlib::reflect>
#include <stdlib::sync>
#include <stdlib::vec>

// The sink at the end: counts what reaches it.
struct Tally { n: long }
methods Tally for Write { write &self ptr:long len:long -> long { self.n = self.n + len; return len; } }

// An inline buffer of N bytes in front of a W.
struct Hold<W, N: long = 16> { inner: W, data: [u8; N], pos: long }
methods Hold<W: Write, N> {
    put &self c:u8 -> void {
        if (self.pos == N) { self.flush(); }
        self.data[self.pos] = c;
        self.pos = self.pos + 1;
    }
    flush &self -> void {
        if (self.pos > 0) {
            unsafe { self.inner.write(&self.data as long, self.pos); }
            self.pos = 0;
        }
    }
    room &self -> long { return N - self.pos; }
}

struct Table<N: long> { v: [long; N], n: long }
tableOf<N: long> -> Table<N> {
    t: Table<N> = Table { n: N };
    for i in 0..N { t.v[i] = i * i; }
    return t;
}

SQUARES: Table<6> = tableOf();
var gHold: Mutex<Hold<Tally, 8>> = Mutex { sl: SpinLock.new(), data: Hold { inner: Tally { n: 0 }, pos: 0 } };
var gDefault: Hold<Tally> = Hold { inner: Tally { n: 0 }, pos: 3 };

// The derive: how many elements a type's arrays hold, read from its declaration.
pub trait Slots derive deriveSlots { slots &self -> long; }
pub macro deriveSlots t:Struct -> Node {
    total: long = 0;
    for i in 0..t.fields.len() {
        f: Field = t.fields.get(i);
        if (f.isArray) { total = total + f.count; }
    }
    n: Node = Node.Int(total);
    return quote { methods @(t.name) for Slots { slots &self -> long { return @n; } } };
}

main -> int {
    if (SQUARES.n != 6 || SQUARES.v[5] != 25 || SQUARES.v[..].len != 6) { return 1; }
    with gHold {
        for i in 0..20 { gHold.data.put(65 as u8); }
        gHold.data.flush();
    }
    if (gHold.data.inner.n != 20 || gHold.data.room() != 8) { return 2; }
    if (gDefault.room() != 13) { return 3; }
    t: Table<3> = tableOf();
    if (SQUARES.slots() != 6 || t.slots() != 3 || gDefault.slots() != 16) { return 4; }
    return 0;
}
