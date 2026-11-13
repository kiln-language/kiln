// The derive refuses what it cannot write: `Link.next` is a raw pointer, an address that means
// nothing in another process. The refusal is the compile's error, naming the type, the field,
// the trait and the function that needed the implementation (`save`, not `main`). `Handle`
// holds a raw pointer too, but writes its own `Encode`, so it is never derived and never refused.
#include <stdlib::encode>

struct Link { value: long, next: *Link }
struct Handle { fd: long, buf: *u8 }
methods Handle for Encode { encode &self out:&Encoder -> void { out.putVarint(self.fd); } }

local save l:Link h:Handle -> long {
    e: Encoder;
    h.encode(e);
    l.encode(e);
    return e.len();
}

main -> int {
    l: Link;
    h: Handle;
    return save(l, h) as int;
}
