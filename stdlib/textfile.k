// Whole-file text: reading a file into a String, or into its lines.
//
//     src: Result<String, long> = readFileString("stdlib/path.k");
//
// Its own module because `io` includes `file` — every program that prints compiles that closure,
// and `String` is not in it. Keeping the String-returning forms here is what stops "hello world"
// from compiling the string machinery, the map it hashes with and the comparison traits behind it.
#include <{file, string, result, vec}>

// The whole file as a String, sized from the file itself so nothing is truncated and no cap has
// to be guessed — and, for a file that reports no size (anything under /proc, a pipe), read
// until it ends. The safe counterpart to `readFile`: this one owns what it read, so the caller
// never sees a raw pointer and the bytes are released with the String.
//
// An empty file is `Ok` with an empty String, not an error — a source file with nothing in it is
// a legitimate thing to read.
pub readFileString path:str -> Result<String, long> {
    o: Result<File, long> = File.openRead(path);
    match o {
        Err(e) { return Result.Err(e); }
        Ok(f)  {
            out: String;
            hint: long = f.size();
            if (hint < 4096) { hint = 4096; }
            loop {
                out.reserve(hint);
                got: long = 0;
                unsafe { got = f.readInto(out.buf as long + out.len, out.cap - out.len); }
                if (got < 0) { return Result.Err(-got); }
                out.len = out.len + got;
                if (out.len < out.cap) { return Result.Ok(out); }    // short: the end
                hint = out.cap;                                       // filled: there may be more
            }
        }
    }
}
