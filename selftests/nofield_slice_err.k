// A slice has `ptr` and `len`, and nothing else.
main -> int { a: [long; 2] = [1, 2]; v: [long] = a[..]; n: long = v.size; return n as int; }
