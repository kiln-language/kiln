// The heap-free containers sized by a length parameter (FixedString<N>, InlineVec<T, N>,
// RingBuffer<T, N>) and the number buffers sized to exactly what a number prints as. Exits 0
// when every check holds, otherwise the number of the first one that did not.
#include <stdlib::io>
#include <stdlib::fixedstring>
#include <stdlib::inlinevec>
#include <stdlib::ring>
#include <stdlib::map>
#include <stdlib::string>
#include <stdlib::time>

struct P { x: long, y: long }

main -> int {
    // FixedString: format into it, read it back, compare, truncate, key a map by it
    s: FixedString<16> = formatFixed("{}:{}", "host", 8080);
    if (s != "host:8080" || s.length() != 9 || s.capacity() != 16 || s.wasCut()) { return 1; }
    t: FixedString<4> = fixedOf("toolong");
    if (t != "tool" || !t.wasCut() || !t.isFull()) { return 2; }
    if (t.push('x') || t.pop().unwrapOr('?') != 'l') { return 3; }
    line: FixedString<32>;
    writeTo(line, "[{:>5}]", 42);
    if (line != "[   42]" || !line.startsWith("[ ") || line.find("42").unwrapOr(-1) != 4) { return 4; }
    shown: String = format("<{}>", s);
    if (shown != "<host:8080>") { return 5; }
    m: HashMap<FixedString<16>, long>;
    m.put(s, 7);
    key: FixedString<16> = fixedOf("host:8080");
    if (m.getOr(key, 0) != 7 || s.toString() != "host:8080") { return 6; }

    // InlineVec: bounded, in place, refuses past N
    v: InlineVec<P, 3>;
    v.push(P { x: 1, y: 2 });
    v.push(P { x: 3, y: 4 });
    if (!v.tryPush(P { x: 5, y: 6 }) || v.tryPush(P { x: 7, y: 8 }) || !v.isFull()) { return 10; }
    v[0].x = 10;
    r: P = v.removeAt(1);
    if (r.x != 3 || v.len() != 2 || v[0].x != 10 || v.last().x != 5) { return 11; }
    if (!v.insert(0, P { x: 0, y: 0 }) || v.get(1).x != 10 || v.swapRemove(0).x != 0 || v.get(0).x != 5) { return 12; }
    w: InlineVec<long, 4>;
    xs: [long; 6];
    // The owning temporary from toVec() sits inside the chain: it must be built after the two
    // calls before it have changed `w` (gap 22, fixed).
    if (w.extendSlice(xs[..]) != 4 || w.tryPop().unwrapOr(-1) != 0 || w.toVec().len() != 3) { return 13; }

    // RingBuffer: both ends, eviction of the oldest, logical indexing
    q: RingBuffer<long, 3>;
    for i in 0..5 { e: Option<long> = q.pushEvict(i); }               // holds 2, 3, 4
    if (q.pushFront(99) || q.front() != 2 || q.back() != 4 || q[1] != 3) { return 20; }
    ev: Option<long> = q.pushEvict(5);
    ordered: Vec<long> = q.toVec();
    if (ev.unwrapOr(-1) != 2 || ordered.get(0) != 3) { return 21; }
    if (q.popBack() != 5 || !q.pushFront(1) || q.tryPopFront().unwrapOr(-1) != 1) { return 22; }
    q.clear();
    if (q.tryPopBack().isSome() || !q.pushBack(7) || q.get(0) != 7) { return 23; }

    // the number buffers are exactly as long as the longest number
    lmin: long = -9223372036854775807 - 1;
    umax: u64 = -1 as u64;
    imin: int = -2147483647 - 1;
    nums: String = format("{} {} {}", lmin, umax, imin);
    if (nums != "-9223372036854775808 18446744073709551615 -2147483648") { return 30; }
    b: String;
    b.pushLong(lmin);
    b.pushULong(umax);
    if (b != "-922337203685477580818446744073709551615") { return 31; }

    // Timespec under the clock and the sleep
    a: Instant = monotonic();
    sleepFor(1000000);
    if (elapsedUs(a) < 1000) { return 40; }
    return 0;
}
