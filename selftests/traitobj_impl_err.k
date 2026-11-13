// A value handed to a trait-object parameter must implement the trait. A `Mutex<BufWriter<Write>>`
// (what `io`'s `gStdout` is) is not a `Write`: this reached the assembler as a vtable naming a
// method nobody defined.
#include <stdlib::{io, fmt, sync, write, file}>
gFile: File = File { fd: 1 };
var gOut: Mutex<BufWriter<Write>> = Mutex {
    sl: SpinLock.new(),
    data: BufWriter { inner: gFile, cap: 4096, pos: 0, mode: BufferMode.Line('\n') }
};
hexOf w:Write n:long -> void { putStr(w, "x"); }
main -> int { hexOf(gOut, 11); return 0; }
