// A field that owns a resource and has no default must be given: zero bytes are no value of it.
#include <stdlib::core>
struct Sock { fd: long }
methods Sock for Drop { drop &self -> void { } }
struct Conn { s: Sock, n: long }
main -> int { c: Conn = Conn { n: 1 }; return c.n as int; }
