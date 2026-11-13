// Sorting and searching any `Vec<T>`.
//
// The ordering comes from the element type — `sort(&xs)` needs nothing else, because `Ord` is a
// bound the body dispatches through:
//
//     xs: Vec<long>;
//     xs.push(3); xs.push(1); xs.push(2);
//     sort(&xs);                                // [1, 2, 3]
//     at: Option<long> = binarySearch(&xs, 2);
//
// When the type's own order is not the one you want, the `*By` forms take a `Compare<T>`:
//
//     sortBy(&xs, ByDesc<long> { });            // [3, 2, 1]
//     sortBy(&xs, ByFn<long> { f: &byLastDigit });  // any function, no type needed
//
// A comparator is a value, so it can carry what the comparison reads. The stateless ones also
// cost LESS than the function pointer they replace: `compare` monomorphizes to a direct call
// the inliner erases, where a `fn` is an indirect call at every comparison and the inliner
// never touches one.
//
// Two algorithms. `sort`/`sortBy` is introsort — quicksort with a median-of-three pivot,
// insertion sort under 16 elements, heapsort once recursion passes 2*log2(n) — in place, and NOT
// stable: ties keep no particular order. `sortStable`/`sortStableBy` is a merge sort that keeps
// equal elements in the order they arrived, at the price of a scratch buffer as large as the
// vector. Pick it when the order of ties means something — records sorted by one key after
// another.
//
// Nothing here copies an element out, so the same code sorts a Vec<String> and a Vec<long>:
// comparisons borrow, and the moves are bitwise shuffles of slots inside a buffer, which is the
// one place a permutation of owning values is safe -- every slot ends up holding exactly one of
// them. The inner loops index the buffer directly: the range is checked once on the way in, and
// a bounds check per element per comparison was a third of the sort.
#include <{core, cmp, vec, heap, mem, option}>

// [lo, hi] is within the vector, or nothing below is sound. Checked once per range.
local checkRange<T> inout v:Vec<T> lo:long hi:long -> void {
    if (lo < 0) { panicIndex("sort", lo, v.len()); }
    if (hi >= v.len()) { panicIndex("sort", hi, v.len()); }
}

// Two slots exchanged bitwise. `t` is an owning local for the duration and is moved back in,
// so nothing is dropped and nothing is duplicated.
local unsafe swapRaw<T> p:*T i:long j:long -> void {
    t: T = p[i];
    p[i] = p[j];
    p[j] = t;
}

// Quadratic in general, but the fastest thing there is on the short, nearly-ordered runs
// quicksort hands it.
local insertionRange<T, C: Compare<T>> inout v:Vec<T> lo:long hi:long c:C -> void {
    if (lo >= hi) { return; }
    checkRange(v, lo, hi);
    unsafe {
        p: *T = v.buf.ptr;
        for i in lo + 1..hi + 1 {
            key: T = p[i];                                  // lifted out; its slot is overwritten below
            j: long = i - 1;
            while (j >= lo && c.compare(p[j], key) > 0) {   // slide the greater ones right, one move each
                p[j + 1] = p[j];
                j = j - 1;
            }
            p[j + 1] = key;                                 // moved back in: one owner per slot again
        }
    }
}

// Partition [lo, hi] around a median-of-three pivot and return where the pivot came to rest:
// everything before it compares <= 0 against it, everything after >= 0. The pivot is moved
// to v[lo] first and stays there while the two scans run, which is what lets it be compared
// against IN PLACE rather than copied out; the last swap puts it where it belongs. Ordering
// the three samples also plants v[hi] >= pivot, the sentinel that stops the upward scan.
local partition<T, C: Compare<T>> inout v:Vec<T> lo:long hi:long c:C -> long {
    checkRange(v, lo, hi);
    unsafe {
        p: *T = v.buf.ptr;
        mid: long = lo + (hi - lo) / 2;
        if (c.compare(p[mid], p[lo]) < 0) { swapRaw(p, mid, lo); }
        if (c.compare(p[hi],  p[lo]) < 0) { swapRaw(p, hi,  lo); }
        if (c.compare(p[hi],  p[mid]) < 0) { swapRaw(p, hi,  mid); }
        swapRaw(p, lo, mid);                              // the median, now at lo, is the pivot
        i: long = lo + 1;
        j: long = hi;
        loop {
            while (c.compare(p[i], p[lo]) < 0) { i = i + 1; }   // stops at hi at the latest
            while (c.compare(p[j], p[lo]) > 0) { j = j - 1; }   // stops at lo at the latest
            if (i >= j) { break; }
            swapRaw(p, i, j);
            i = i + 1;
            j = j - 1;
        }
        swapRaw(p, lo, j);
        return j;
    }
}

// Sift v[start] down through the max-heap rooted in [lo, hi].
local siftDown<T, C: Compare<T>> inout v:Vec<T> lo:long start:long hi:long c:C -> void {
    root: long = start;
    unsafe {
        p: *T = v.buf.ptr;                                // [lo, hi] was checked by heapRange
        loop {
            child: long = lo + (root - lo) * 2 + 1;
            if (child > hi) { return; }
            if (child + 1 <= hi && c.compare(p[child], p[child + 1]) < 0) { child = child + 1; }
            if (c.compare(p[root], p[child]) >= 0) { return; }
            swapRaw(p, root, child);
            root = child;
        }
    }
}

// Guaranteed O(n log n), in place, no recursion, no bad case — the ceiling that keeps
// introsort's worst case honest.
local heapRange<T, C: Compare<T>> inout v:Vec<T> lo:long hi:long c:C -> void {
    n: long = hi - lo + 1;
    if (n < 2) { return; }
    checkRange(v, lo, hi);
    i: long = lo + n / 2 - 1;
    while (i >= lo) {
        siftDown(v, lo, i, hi, c);
        i = i - 1;
    }
    e: long = hi;
    while (e > lo) {
        v.swap(lo, e);
        e = e - 1;
        siftDown(v, lo, lo, e, c);
    }
}

// Quicksort [lo, hi] with `budget` levels left before bailing out to heapsort. Recursion
// always descends into the SMALLER partition and loops on the larger, so stack depth stays
// O(log n) however lopsided the splits are.
local introRange<T, C: Compare<T>> inout v:Vec<T> lo:long hi:long c:C budget:long -> void {
    while (lo < hi) {
        if (hi - lo < 16) { insertionRange(v, lo, hi, c); return; }
        if (budget <= 0) { heapRange(v, lo, hi, c); return; }
        budget = budget - 1;
        p: long = partition(v, lo, hi, c);
        if (p - lo < hi - p) {
            introRange(v, lo, p - 1, c, budget);
            lo = p + 1;
        } else {
            introRange(v, p + 1, hi, c, budget);
            hi = p - 1;
        }
    }
}

// ─── the stable sort ────────────────────────────────────────────────────────
// Bottom-up merge sort: runs of 16 sorted by insertion (which is stable — it moves an element
// only past strictly greater ones), then merged in widening passes, back and forth between the
// vector's buffer and a scratch buffer of the same size. A tie takes the LEFT run's element
// first, which is the whole of stability. Elements move by bytes, as everywhere here.

// Merge [lo, mid) and [mid, hi) of `src` into the same positions of `dst`.
local unsafe mergeRuns<T, C: Compare<T>> src:*T dst:*T lo:long mid:long hi:long c:C -> void {
    i: long = lo;
    j: long = mid;
    k: long = lo;
    while (i < mid && j < hi) {
        if (c.compare(src[j], src[i]) < 0) { memcpy(dst + k, src + j, sizeof(T)); j = j + 1; }
        else                               { memcpy(dst + k, src + i, sizeof(T)); i = i + 1; }
        k = k + 1;
    }
    if (i < mid) { memcpy(dst + k, src + i, (mid - i) * sizeof(T)); }
    if (j < hi)  { memcpy(dst + k, src + j, (hi - j) * sizeof(T)); }
}

pub sortStableBy<T, C: Compare<T>> inout v:Vec<T> c:C -> void {
    n: long = v.len();
    if (n < 2) { return; }
    run: long = 16;
    first: long = 0;
    while (first < n) {
        last: long = first + run - 1;
        if (last >= n) { last = n - 1; }
        insertionRange(v, first, last, c);
        first = first + run;
    }
    if (n <= run) { return; }
    unsafe {
        a: *T = v.buf.ptr;
        b: *T = malloc(n * sizeof(T)) as *T;
        inA: bool = true;                                  // which buffer holds the current runs
        width: long = run;
        while (width < n) {
            src: *T = a; dst: *T = b;
            if (!inA) { src = b; dst = a; }
            lo: long = 0;
            while (lo < n) {
                mid: long = lo + width;
                if (mid > n) { mid = n; }
                hi: long = mid + width;
                if (hi > n) { hi = n; }
                mergeRuns(src, dst, lo, mid, hi, c);
                lo = hi;
            }
            inA = !inA;
            width = width * 2;
        }
        if (!inA) { memcpy(a, b, n * sizeof(T)); }         // the result ended in the scratch
        free(b);                                           // only bytes: every value lives in `a`
    }
}

// ─── ordered by a comparator ────────────────────────────────────────────────

pub sortBy<T, C: Compare<T>> inout v:Vec<T> c:C -> void {
    n: long = v.len();
    if (n < 2) { return; }
    lg: long = 0;                       // floor(log2 n)
    m: long = n;
    while (m > 1) { m = m / 2; lg = lg + 1; }
    introRange(v, 0, n - 1, c, lg * 2);
}

pub isSortedBy<T, C: Compare<T>> inout v:Vec<T> c:C -> bool {
    for i in 1..v.len() {
        if (c.compare(v[i - 1], v[i]) > 0) { return false; }
    }
    return true;
}

// The index of `key` in a vector already sorted by `c`, or nothing. Which of several equal
// elements you get is unspecified.
pub binarySearchBy<T, C: Compare<T>> inout v:Vec<T> key:T c:C -> Option<long> {
    lo: long = 0;
    hi: long = v.len() - 1;
    while (lo <= hi) {
        mid: long = lo + (hi - lo) / 2;
        r: int = c.compare(v[mid], key);
        if (r == 0) { return Option.Some(mid); }
        if (r < 0)  { lo = mid + 1; }
        else        { hi = mid - 1; }
    }
    return Option.None;
}

// The first index `key` could be inserted at while keeping the vector sorted; len() when it
// sorts after everything. Always an index, so no Option: there is no "absent" answer.
pub lowerBoundBy<T, C: Compare<T>> inout v:Vec<T> key:T c:C -> long {
    lo: long = 0;
    hi: long = v.len();
    while (lo < hi) {
        mid: long = lo + (hi - lo) / 2;
        if (c.compare(v[mid], key) < 0) { lo = mid + 1; } else { hi = mid; }
    }
    return lo;
}
// The LAST such index: past every element equal to `key`. [lowerBound, upperBound) is the
// run of elements equal to it.
pub upperBoundBy<T, C: Compare<T>> inout v:Vec<T> key:T c:C -> long {
    lo: long = 0;
    hi: long = v.len();
    while (lo < hi) {
        mid: long = lo + (hi - lo) / 2;
        if (c.compare(key, v[mid]) < 0) { hi = mid; } else { lo = mid + 1; }
    }
    return lo;
}

// ─── ordered by the element type ────────────────────────────────────────────
// The same, at ByOrd. Stateless, so these cost a monomorphized copy and nothing at runtime —
// the comparator is not passed, it is compiled in.

pub sort<T: Ord> inout v:Vec<T> -> void { sortBy(v, ByOrd<T> { }); }
pub sortStable<T: Ord> inout v:Vec<T> -> void { sortStableBy(v, ByOrd<T> { }); }
pub isSorted<T: Ord> inout v:Vec<T> -> bool { return isSortedBy(v, ByOrd<T> { }); }
pub binarySearch<T: Ord> inout v:Vec<T> key:T -> Option<long> { return binarySearchBy(v, key, ByOrd<T> { }); }
pub lowerBound<T: Ord> inout v:Vec<T> key:T -> long { return lowerBoundBy(v, key, ByOrd<T> { }); }
pub upperBound<T: Ord> inout v:Vec<T> key:T -> long { return upperBoundBy(v, key, ByOrd<T> { }); }
