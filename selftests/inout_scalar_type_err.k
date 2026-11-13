inc inout n:long -> void { n = n + 1; }
main -> int { n: int = 1; inc(&n); return n; }
