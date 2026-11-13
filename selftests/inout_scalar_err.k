inc inout n:long -> void { n = n + 1; }
main -> int { n: long = 1; inc(n); return n as int; }
