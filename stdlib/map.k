// HashMap<K, V> — open-addressed with linear probing.
//
// Open addressing rather than chaining: no per-entry allocation, and a probe walks forward
// through contiguous memory instead of chasing pointers. Capacity is a power of two so the
// bucket index is a mask, and the table rehashes once it is three-quarters full, past which
// probe sequences get long fast.
//
// A removed slot becomes a TOMBSTONE, not an empty one, so a probe can still walk past it to a
// key inserted after the collision. Tombstones count toward the load factor, so a churn-heavy
// table rehashes and cleans them out.
//
// Three parallel typed arrays rather than one array of {state, key, value}: no padding
// questions between a K and a V of different sizes, and a probe walks a byte-per-slot state
// array — 64 slots per cache line — instead of striding over whole entries.
//
// HOW KEYS ARE COMPARED. The key type answers for itself: `Hash` gives the bucket and `==`
// decides a match, so `str` keys work — they hash and compare by CONTENT, where hashing the
// bytes of the {ptr, len} header would have made two equal strings at different addresses miss
// each other. A scalar compares natively and a plain struct derives its `==`, so neither has
// anything to write.
//
//     m: HashMap<int, long>;            // Default: empty, no allocation
//     m.put(1, 100);
//     if (m.has(1)) { println("{}", m.get(1)); }
//     println("{}", m.getOr(99, -1));   // absent -> the fallback
//     f: Option<long> = m.find(2);      // absent -> None
//
//     names: HashMap<str, long>;        // and this one now means what it reads as
//     names.put("gamma", 3);
//
// And written as a literal, `map![k => v, ...]` -- see the macro at the end of this file:
//
//     ranks: HashMap<str, long> = map!["gamma" => 3, "delta" => 4];
//     none:  HashMap<str, long> = map![];
#include <{core, panic, cmp, option, heap, mem, string, chars, vec}>

// `get` and the slot accessors end the program when what they were promised is not there.
// `find`, `has` and `getOr` are the ways to ask without promising.

// Where a key is, or where it would go. One fact rather than an index plus a flag that could
// disagree, and no index value has to stand in for "nowhere".
local enum Probe {
    Found(long),        // the Full slot already holding the key
    Vacant(long),       // the slot it should be inserted into
    NoRoom              // no capacity at all, or every slot walked without finding either
}

// One byte per slot: a probe stops at Empty, walks past Tomb, compares at Full. Empty is 0 so
// a fresh state array is a zero fill.
local enum SlotState: u8 { Empty, Full, Tomb }

// The bound sits on the STRUCT, not on the methods block, so a key type without `Hash` is
// refused where it is named — a block-level bound would instead quietly drop every method and
// report a missing `put` much later.
pub struct HashMap<K: Hash, V> {
    states: *u8,    // cap bytes, one SlotState per slot
    keys:   *K,     // cap keys
    vals:   *V,     // cap values
    cap:    long,   // 0, or a power of two
    count:  long,   // live entries
    dead:   long    // tombstones
}

// A map of the pairs, key i with value i: what `map![k => v, ...]` expands to. The keys arrive
// as a Vec because a call has one variadic; the values are it.
pub mapOf<K: Hash, V: Copy> sink keys:Vec<K> vals:...V -> HashMap<K, V> {
    m: HashMap<K, V>;
    if (keys.len() != vals.len) { panic("mapOf: as many keys as values"); }
    m.reserve(vals.len);
    while (keys.len() > 0) {
        i: long = keys.len() - 1;
        m.put(keys.pop(), vals[i]);
    }
    return m;
}
// An empty one, as an expression: `map![]`. K and V come from where the result is stored.
pub emptyMap<K: Hash, V> -> HashMap<K, V> { m: HashMap<K, V>; return m; }

methods HashMap<K, V> for Default {
    new -> HashMap<K, V> {
        unsafe { return HashMap { states: 0 as *u8, keys: 0 as *K, vals: 0 as *V, cap: 0, count: 0, dead: 0 }; }
    }
}

methods HashMap<K, V> for Drop {
    drop &self -> void {
        self.clear();                                    // releases the live entries, if K or V needs it
        unsafe {
            if (self.cap > 0) {
                free(self.states);
                free(self.keys);
                free(self.vals);
            }
        }
    }
}

// Any key and value type. An entry is reached in place -- `m[k]`, `keyAt(i)`, `valAt(i)` are
// borrows -- and moved in by `put`; only the accessors that hand out a COPY (`get`, `getOr`,
// `find`) ask for `Copy`, further down.
methods HashMap<K, V> {
    len     &self -> long { return self.count; }
    cap     &self -> long { return self.cap; }
    isEmpty &self -> bool { return self.count == 0; }

    // Is slot i live? With keyAt/valAt this is how you iterate: walk 0..cap() and skip the
    // slots that are not occupied.
    occupied &self i:long -> bool {
        if (i < 0 || i >= self.cap) { return false; }
        unsafe { return self.states[i] == SlotState.Full; }
    }
    // The first live slot after `i`, or -1 when there is none: `nextSlot(-1)` is the first. The
    // walk without testing every empty slot by hand:
    //
    //     i: long = m.nextSlot(-1);
    //     while (i >= 0) { use(m.keyAt(i), m.valAt(i)); i = m.nextSlot(i); }
    nextSlot &self i:long -> long {
        j: long = i + 1;
        if (j < 0) { j = 0; }
        while (j < self.cap) {
            if (self.occupied(j)) { return j; }
            j = j + 1;
        }
        return -1;
    }
    keyAt &self i:long -> &K {
        if (!self.occupied(i)) { panicIndex("HashMap.keyAt: slot is not occupied", i, self.cap); }
        unsafe { return self.keys[i]; }
    }
    valAt &self i:long -> &V {
        if (!self.occupied(i)) { panicIndex("HashMap.valAt: slot is not occupied", i, self.cap); }
        unsafe { return self.vals[i]; }
    }

    // A tombstone seen on the way is remembered and preferred over the empty slot the walk
    // ends at, so repeated insert/remove of one key reuses its slot instead of drifting.
    probe &self k:K -> Probe {
        if (self.cap == 0) { return Probe.NoRoom; }

        mask: long = self.cap - 1;
        firstTomb: long = -1;
        h: u64 = k.hash();
        idx: long = (h as long) & mask;      // cap is a power of two, so the mask IS the modulo

        for n in 0..self.cap {
            st: u8 = 0;
            unsafe { st = self.states[idx]; }
            if (st == SlotState.Empty) {
                if (firstTomb >= 0) { return Probe.Vacant(firstTomb); }
                return Probe.Vacant(idx);
            }
            if (st == SlotState.Tomb) {
                if (firstTomb < 0) { firstTomb = idx; }
            }
            else {
                unsafe { if (self.keys[idx] == k) { return Probe.Found(idx); } }
            }
            idx = (idx + 1) & mask;
        }
        if (firstTomb >= 0) { return Probe.Vacant(firstTomb); }
        return Probe.NoRoom;
    }

    // Grow to at least `need` slots (power of two, minimum 8) and rehash, dropping tombstones
    // on the way — which is what keeps a churn-heavy table fast.
    rehash &self need:long -> void {
        ncap: long = 8;
        while (ncap < need) { ncap = ncap * 2; }

        oldCap: long = self.cap;
        unsafe {
            oldStates: *u8 = self.states;
            oldKeys:   *K  = self.keys;
            oldVals:   *V  = self.vals;

            self.states = malloc(ncap) as *u8;
            self.keys   = malloc(ncap * sizeof(K)) as *K;
            self.vals   = malloc(ncap * sizeof(V)) as *V;
            memset(self.states, SlotState.Empty as long, ncap);
            self.cap    = ncap;
            self.count  = 0;
            self.dead   = 0;

            for i in 0..oldCap {                             // re-insert every live entry
                if (oldStates[i] == SlotState.Full) { self.put(oldKeys[i], oldVals[i]); }
            }
            if (oldCap > 0) {
                free(oldStates);
                free(oldKeys);
                free(oldVals);
            }
        }
    }

    // Room for `additional` more entries without a rehash.
    reserve &self additional:long -> void {
        want: long = (self.count + additional) * 2;
        if (want > self.cap) { self.rehash(want); }
    }

    // Insert, or overwrite the value if the key is already there.
    put &self k:K v:V -> void {
        // Three-quarters full, counting tombstones, is when probe sequences start to get long.
        // But WHICH of the two filled it decides what to do: more room only helps if live
        // entries need it, so when tombstones are what crossed the line, rehash at the SAME
        // capacity to sweep them out. Doubling instead would answer churn by taking memory it
        // already had — a table holding 49 keys reached 2048 slots that way.
        if ((self.count + self.dead + 1) * 4 > self.cap * 3) {
            if ((self.count + 1) * 4 > self.cap * 3) { self.rehash(self.cap * 2 + 8); }
            else                                     { self.rehash(self.cap); }
        }

        pr: Probe = self.probe(k);
        match pr {
            Found(fi)  {
                unsafe {
                    old: V = self.vals[fi];              // moved out, so it is this scope's to drop
                    self.vals[fi] = v;
                }
            }
            Vacant(vi) {
                unsafe {
                    if (self.states[vi] == SlotState.Tomb) { self.dead = self.dead - 1; }
                    self.keys[vi]   = k;
                    self.states[vi] = SlotState.Full;
                    self.vals[vi]   = v;
                }
                self.count = self.count + 1;
            }
            NoRoom { panicState("HashMap.put", "the table is full and could not grow"); }
        }
    }

    has &self k:K -> bool {
        pr: Probe = self.probe(k);
        match pr {
            Found(_) { return true; }
            _        { return false; }
        }
    }

    // Returns whether the key was there. The slot becomes a tombstone so probes for keys
    // inserted after it can still walk past; the entry it held is released.
    remove &self k:K -> bool {
        pr: Probe = self.probe(k);
        match pr {
            Found(ri) {
                unsafe {
                    goneK: K = self.keys[ri];            // moved out: this scope releases them
                    goneV: V = self.vals[ri];
                    self.states[ri] = SlotState.Tomb;
                }
                self.count = self.count - 1;
                self.dead  = self.dead + 1;
                return true;
            }
            _ { return false; }
        }
    }

    // Remove the key and hand its value back, or nothing if it was not there. The key the
    // table held is released; the value is the caller's now.
    take &self k:K -> Option<V> {
        pr: Probe = self.probe(k);
        match pr {
            Found(ri) {
                v: V;
                unsafe {
                    goneK: K = self.keys[ri];
                    v = self.vals[ri];
                    self.states[ri] = SlotState.Tomb;
                }
                self.count = self.count - 1;
                self.dead  = self.dead + 1;
                return Option.Some(v);
            }
            _ { return Option.None; }
        }
    }

    // Forget every entry, keep the allocation. Releases the entries when K or V needs it.
    clear &self -> void {
        unsafe {
            for i in 0..self.cap {
                if (self.states[i] == SlotState.Full) {
                    goneK: K = self.keys[i];
                    goneV: V = self.vals[i];
                }
            }
            if (self.cap > 0) { memset(self.states, SlotState.Empty as long, self.cap); }
        }
        self.count = 0;
        self.dead  = 0;
    }
}

// `m[k]` is a borrow of the value, trapping if the key is absent -- the in-place form of
// `get`, and the one that works for an owning V. `m[k] = v` is `put`.
methods HashMap<K, V> for Index<K, V> {
    at &self k:K -> &V {
        pr: Probe = self.probe(k);
        match pr {
            Found(gi) { unsafe { return self.vals[gi]; } }
            _         { panicState("HashMap.at", "no such key — use find or has"); }
        }
    }
}
methods HashMap<K, V> for IndexSet<K, V> {
    setAt &self k:K v:V -> void { self.put(k, v); }
}

// Reading a value OUT hands out a copy, which only a Copy value has to give.
// A deep copy (see Vec's Clone for why it has to be written out).
methods HashMap<K: Clone, V: Clone> for Clone {
    clone &self -> HashMap<K, V> {
        out: HashMap<K, V>;
        out.reserve(self.count);
        i: long = self.nextSlot(-1);
        while (i >= 0) {
            out.put(self.keyAt(i).clone(), self.valAt(i).clone());
            i = self.nextSlot(i);
        }
        return out;
    }
}

methods HashMap<K, V: Copy> {
    // THE lookup: absence is an ordinary outcome for a map, and this is the accessor that can
    // say so without trapping or being handed a value of V to stand in for "not there". `get`
    // and `getOr` predate it and stay because each is shorter when you know the key is there
    // or you have a real default.
    //
    // Every method of a generic type is stamped per instantiation whether it is called or not,
    // so this instantiates `Option<V>` for every map in the program. Worth it here, unlike
    // Result's conversions: reporting absence is a map's primary operation, not a side trip.
    find &self k:K -> Option<V> {
        pr: Probe = self.probe(k);
        match pr {
            Found(i) { unsafe { v: V = self.vals[i]; return Option.Some(v); } }
            _        { return Option.None; }
        }
    }

    // Traps if the key is absent. Use `find`, `has` or `getOr` when absence is normal.
    get &self k:K -> V {
        pr: Probe = self.probe(k);
        match pr {
            Found(gi) { unsafe { return self.vals[gi]; } }
            _         { panicState("HashMap.get", "no such key — use find, has or getOr"); }
        }
    }

    getOr &self k:K dflt:V -> V {
        pr: Probe = self.probe(k);
        match pr {
            Found(oi) { unsafe { return self.vals[oi]; } }
            _         { return dflt; }
        }
    }

    // Every value, in slot order (which is no order a caller should rely on).
    values &self -> Vec<V> {
        out: Vec<V>;
        out.reserve(self.count);
        unsafe { for i in 0..self.cap { if (self.states[i] == SlotState.Full) { out.push(self.vals[i]); } } }
        return out;
    }
}

methods HashMap<K: Copy, V> {
    // Every key, in slot order. Copies, so a Copy key; an owning key is walked with `nextSlot`.
    keys &self -> Vec<K> {
        out: Vec<K>;
        out.reserve(self.count);
        unsafe { for i in 0..self.cap { if (self.states[i] == SlotState.Full) { out.push(self.keys[i]); } } }
        return out;
    }
}

// `map!["a" => 1, "b" => 2]`: a `HashMap` of the pairs, as the call `mapOf(vecOf("a", "b"), 1, 2)`;
// `map![]` is an empty one. Both are typed by where they are stored; `map![str, long: ...]`
// names the key and value types outright. The source reaches the macro respelled token by
// token, so the arrow may read `= >`.
pub macro map src:str -> Node {
    t: RawText = takePrefix(src, 2);
    kname: str = "";
    vname: str = "";
    if (t.names.len() == 2) { kname = t.names.get(0); vname = t.names.get(1); }
    pieces: Vec<str> = splitTopLevel(t.rest, "map!");
    if (pieces.len() == 0) { return Node.Call("emptyMap", parseEach(pieces, "")); }
    keys: Vec<str>;
    vals: Vec<str>;
    for pair in pieces {
        at: long = arrowAt(pair);
        if (at < 0) { panic("map!: an element is `key => value`"); }
        after: long = at + 1;
        while (charAt(pair, after) != '>') { after = after + 1; }
        after = after + 1;
        keys.push(strTrim(strSlice(pair, 0, at)));
        vals.push(strTrim(strSlice(pair, after, pair.len - after)));
    }
    args: Vec<Node>;
    args.push(Node.Call("vecOf", parseEach(keys, kname)));
    for v in vals {
        e: Node = parseExpr(v);
        if (vname.len > 0) { e = Node.Cast(newBox(e), vname); }
        args.push(e);
    }
    return Node.Call("mapOf", args);
}

// Where the first top-level `=>` begins, or -1: the `=` is the only bare one an element can hold.
local arrowAt s:str -> long {
    depth: long = 0;
    i: long = 0;
    while (i < s.len) {
        c: long = charAt(s, i);
        if (c == '"' || c == '\'') { i = literalEnd(s, i); continue; }
        if (c == '(' || c == '[' || c == '{') { depth = depth + 1; }
        if (c == ')' || c == ']' || c == '}') { depth = depth - 1; }
        if (c == '=' && depth == 0) {
            j: long = i + 1;
            while (j < s.len && charAt(s, j) == ' ') { j = j + 1; }
            if (j < s.len && charAt(s, j) == '>') { return i; }
        }
        i = i + 1;
    }
    return -1;
}
