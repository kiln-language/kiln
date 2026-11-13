// An array literal for an array field names every element.
struct S { xs: [long; 3], n: long }
main -> long { s: S = S { xs: [1, 2], n: 4 }; return s.n; }
