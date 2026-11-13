// `&arr` of an array local, a field array and an `inout` parameter's array, handed to an
// `inout [T]` parameter: the lend of its elements, as `&arr[..]` is. 10 + 20 + 7 = 37.
fill inout xs:[long] v:long -> void { for i in 0..xs.len { xs[i] = v; } }
sum xs:[long] -> long { t: long = 0; for x in xs { t = t + x; } return t; }
struct H { cells: [long; 2] }
refill inout h:H -> void { fill(&h.cells, 7); }
main -> int {
    arr: [long; 4];
    fill(&arr, 2);
    h: H = H { };
    fill(&h.cells, 10);
    t: long = sum(arr[..]) + sum(h.cells[..]);
    refill(&h);
    return (t - 8 + h.cells[0] + 10) as int;
}
