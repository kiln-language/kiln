// An error past the parser says where, as the parser's do: the statement it is in, inside a
// generic body stamped for the instance that made it wrong. `file:line:col: Error: ...`.
struct Pair<T> { a: T, b: T }
methods Pair<T> {
    widest &self -> long {
        n: long = 0;
        while (n < 3) {
            if (n == 1) {
                s: str = self.a;
                return s.len;
            }
            n = n + 1;
        }
        return n;
    }
}
main -> int {
    p: Pair<long> = Pair { a: 1, b: 2 };
    return p.widest() as int;
}
