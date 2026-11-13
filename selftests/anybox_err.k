// `any` is a 24-byte box the lowerer builds from six shapes. A slice is not one of them: its
// first word was stored as if it were the whole value.
#include <stdlib::io>
main -> int {
    unsafe {
        b: [u8] = "ab" as [u8];
        println("{}", b);
    }
    return 0;
}
