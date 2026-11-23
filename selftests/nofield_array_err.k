// A fixed array's length is part of its type, not a field.
main -> int { a: [long; 3] = [1, 2, 3]; return a.len as int; }
