// The built-in `assert!` fails through the program's `@panic` function; this program has none.
main -> long { x: long = 3; assert!(x == 3); return 0; }
