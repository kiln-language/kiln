// What the 2026-11-11 standard library review added, held to an exit code: 0 when every check
// holds, otherwise the number of the first one that did not. See STDLIB_REVIEW.md.
#include <stdlib::io>
#include <stdlib::string>
#include <stdlib::map>
#include <stdlib::sort>
#include <stdlib::iter>
#include <stdlib::algo>
#include <stdlib::pool>
#include <stdlib::deque>
#include <stdlib::cmp>
#include <stdlib::bytes>
#include <stdlib::pathbuf>
#include <stdlib::time>
#include <stdlib::thread>
#include <stdlib::heap>
#include <stdlib::mem>

struct R { k: long, id: long }
byK a:R b:R -> int { return a.k.cmp(b.k); }
odd x:long -> bool { return x % 2 == 1; }

struct Loud { id: long }
var gDropped: long = 0;
methods Loud for Drop { drop &self -> void { gDropped = gDropped + self.id; } }

struct Wide { a: long, pad: [long; 18], z: long }      // 160 bytes

var gThreadOut: long = 0;
deep n:long -> long { pad: [long; 32]; pad[0] = n; if (n == 0) { return 0; } return deep(n - 1) + 1; }
worker ctrl:long -> void { gThreadOut = deep(threadArg(ctrl)); }

// A BufWriter in each mode over a capture buffer: what reached the buffer after each write.
bufferModes -> long {
    mem: [u8; 64];
    sw: StringWriter;
    unsafe { sw = stringWriter(&mem as long, 64); }
    w: BufWriter<StringWriter> = bufWriterWith(sw, BufferMode.Delimited("--"));
    putStr(w, "ab-");
    if (w.inner.len != 0) { return 1; }                // no delimiter yet
    putStr(w, "-c");
    if (w.inner.len != 0) { return 2; }                // "--" is inside, not at the end
    putStr(w, "--");
    if (w.inner.len != 7) { return 3; }                // now it ends the buffer: all 7 out
    w.setMode(BufferMode.Line(';'));
    putStr(w, "x;");
    if (w.inner.len != 9) { return 4; }
    w.setMode(BufferMode.Block);
    putStr(w, "y;\n");
    if (w.inner.len != 9) { return 5; }                // held until flushed
    w.flush();
    if (w.inner.len != 12) { return 6; }
    w.setMode(BufferMode.Unbuffered);
    putStr(w, "z");
    if (w.inner.len != 13) { return 7; }
    return 0;
}

main -> long {
    b: long = bufferModes();
    if (b != 0) { return 10 + b; }

    // string.k
    if (strSplitOn("a::b::", "::").len() != 3) { return 20; }
    if (strCount("aaaa", "aa") != 2) { return 21; }
    if (parseLongBase("-ff", 16).unwrapOr(0) != -255) { return 22; }
    if (parseLong("-9223372036854775808").isNone() || parseLong("9223372036854775808").isSome()) { return 23; }
    if (strTrimSet("--x--", "-") != "x" || strTrimEnd(" y ") != " y") { return 24; }
    s: String = stringOf("ab");
    s.makeUpper();
    s.pushRepeated('!', 2);
    if (s != "AB!!" || s.pop().unwrapOr('?') != '!') { return 25; }

    // fmt.k: a Display value honours width and alignment
    p: String = format("[{:>6}]", s);
    if (p != "[   AB!]") { return 30; }

    // cmp.k / bytes.k
    if (maxOf(3 as long, 9 as long) != 9 || clampTo(15 as long, 0 as long, 10 as long) != 10) { return 40; }
    if (orderOf(-5) != Ordering.Less) { return 41; }
    if (bytesCompare("abc" as [u8], "abd" as [u8]) >= 0) { return 42; }

    // sort.k: stable means equal keys keep their order
    v: Vec<R>;
    for i in 0..500 { v.push(R { k: (i * 7919) % 7, id: i }); }
    sortStableBy(&v, ByFn<R> { f: &byK });
    for i in 1..v.len() {
        x: R = v.get(i - 1); y: R = v.get(i);
        if (x.k > y.k || (x.k == y.k && x.id > y.id)) { return 50; }
    }
    w: Vec<long> = vec![1, 2, 2, 2, 5];
    if (lowerBound(&w, 2) != 1 || upperBound(&w, 2) != 4) { return 51; }

    // iter.k: adapters with constructors, a stepped range, and Filter over any T
    t: Take<long, Skip<long, Filter<long, Range>>> = takeIter(skipIter(filter(range(0, 100), &odd), 2), 3);
    if (lastOf(&t).unwrapOr(-1) != 9) { return 60; }
    sr: StepRange = rangeStep(10, 0, -3);
    if (collect(&sr).len() != 4) { return 61; }

    // map.k, pool.k, deque.k, vec.k
    m: HashMap<str, long> = map::map!["a" => 1, "b" => 2];   // qualified: algo has a `map` too
    if (m.take("b").unwrapOr(0) != 2 || m.len() != 1) { return 70; }
    pl: Pool<long>;
    h: Handle = pl.alloc(5);
    pl.free(h);
    if (pl.isLive(h)) { return 71; }
    q: Deque<long>;
    if (q.tryPopFront().isSome()) { return 72; }
    xs: Vec<long> = vec![1, 2, 3, 4, 5, 6];
    retain(&xs, |n: &long| n % 2 == 0);
    xs.truncate(2);
    if (xs.len() != 2 || xs.first() != 2 || xs.tryPop().unwrapOr(0) != 4) { return 73; }

    // heap.k: Rc and Arc release their value with the last handle
    { a: Rc<Loud> = newRc(Loud { id: 1 }); a2: Rc<Loud> = a.clone(); }
    { c: Arc<Loud> = newArc(Loud { id: 10 }); }
    if (gDropped != 11) { return 80; }

    // mem.k: replace / swapValues / take move by exchange and release nothing on the way;
    // each value is released once, by its last owner (ids 100 + 200 + 400 + 800 here)
    gDropped = 0;
    {
        x: Loud = Loud { id: 100 };
        y: Loud = Loud { id: 200 };
        swapValues(&x, &y);
        if (x.id != 200 || y.id != 100 || gDropped != 0) { return 81; }
        old: Loud = replace(&x, Loud { id: 400 });
        if (old.id != 200 || x.id != 400 || gDropped != 0) { return 82; }
        big: Wide = Wide { a: 3, z: 0 };                     // past swapBytes' 64-byte scratch
        other: Wide = Wide { a: 0, z: 7 };
        swapValues(&big, &other);
        if (big.a != 0 || big.z != 7 || other.a != 3 || other.z != 0) { return 83; }
        v: Vec<Loud>; v.push(Loud { id: 800 });
        gone: Loud = replace(v.at(0), Loud { id: 0 });
        if (gone.id != 800 || gDropped != 0) { return 84; }
    }
    if (gDropped != 1500) { return 85; }

    // path / time / thread
    if (normalizePath("/../x") != "/x") { return 90; }
    st: Instant = monotonic();
    if (st.plusNanos(-1500000000).nanos < 0) { return 91; }
    th: Thread = spawnWithStack(&worker, 3000, 4 * 1024 * 1024);
    th.join();
    if (gThreadOut != 3000) { return 92; }
    return 0;
}
