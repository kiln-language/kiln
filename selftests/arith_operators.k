// `-` `*` `/` `%` on a type of your own, the way `+` already did: a call to the operator's trait.
//
// Each was a silent hole. An aggregate flows as a pointer, so `a - b` subtracted the two addresses
// and read the difference back as the struct type, with no diagnostic and an answer that moved with
// the frame layout. `ordmissing_err.k` and `arithmissing_err.k` cover the refusal side.
//
// Exit code: (10-3) + (10*3) + (10/3) + (10%3) = 7 + 30 + 3 + 1 = 41.
#include <stdlib::io>

struct N { v: long }

methods N for Sub<N> { sub self other:N -> N { return N { v: self.v - other.v }; } }
methods N for Mul<N> { mul self other:N -> N { return N { v: self.v * other.v }; } }
methods N for Div<N> { div self other:N -> N { return N { v: self.v / other.v }; } }
methods N for Rem<N> { rem self other:N -> N { return N { v: self.v % other.v }; } }

main -> int {
    a: N = N { v: 10 };
    b: N = N { v: 3 };
    d: N = a - b;
    m: N = N { v: 10 } * N { v: 3 };
    q: N = N { v: 10 } / N { v: 3 };
    r: N = N { v: 10 } % N { v: 3 };
    println("sub={} mul={} div={} rem={}", d.v, m.v, q.v, r.v);
    return (d.v + m.v + q.v + r.v) as int;
}
