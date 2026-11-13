// A type is named as it is written: an instance by its template and arguments, a declared type
// by its bare name when no other type has it, never by the mangled `errspell_err::Box_long`.
struct Box<T> { v: T }
take b:Box<long> -> long { return b.v; }
main -> int { b: Box<str> = Box { v: "x" }; return take(b) as int; }
