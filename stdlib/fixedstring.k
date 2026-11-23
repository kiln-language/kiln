// FixedString<N>: text of at most N bytes, held inline: a string you can build and format into
// without the heap, and without lending anyone a pointer.
//
//     s: FixedString<64> = formatFixed("{}:{}", host, port);
//     line: FixedString<80>;
//     writeTo(line, "{:>8} {}", n, name);      // a Write sink, like String
//     println("{}", line);                     // and Display
//
// What `StringWriter` does, without its `unsafe`: that one points at a buffer the caller owns
// and has to be trusted to outlive the writer; this one is the buffer, so there is nothing to
// trust. It is plain data with no Drop and nothing to release, and a copy is a copy of the bytes.
//
// A write past N keeps what fits and marks the string `wasCut`, the way `StringWriter` truncates;
// `pushStr` and `push` also answer whether everything fit.
#include <{core, mem, fmt, string, cmp, option}>

pub struct FixedString<N: long> { data: [u8; N], len: long, cut: bool }

methods FixedString<N> for Default {
    new -> FixedString<N> { return FixedString { len: 0, cut: false }; }    // data: zero-filled
}

// Appending is writing, so the formatter can aim at one. Answers how much fit.
methods FixedString<N> for Write {
    write &self ptr:long len:long -> long {
        n: long = len;
        if (n > N - self.len) { n = N - self.len; self.cut = true; }
        if (n > 0) { unsafe { memcpy(&self.data as long + self.len, ptr, n); } }
        self.len += n;
        return n;
    }
}

methods FixedString<N> for Display {
    display &self w:Write -> void { putStr(w, self.data[..self.len] as str); }
}

methods FixedString<N> {
    length   &self -> long { return self.len; }
    capacity &self -> long { return N; }
    isEmpty  &self -> bool { return self.len == 0; }
    isFull   &self -> bool { return self.len == N; }
    // Did a write not fit, since this was made or last cleared?
    wasCut   &self -> bool { return self.cut; }
    clear    &self -> void { self.len = 0; self.cut = false; }
    // Keep the first `n` bytes (all of them, if there are fewer).
    truncate &self n:long -> void { if (n >= 0 && n < self.len) { self.len = n; } }

    // Append; false (and `wasCut`) when it did not all fit, in which case what fit was kept.
    push &self c:char -> bool {
        if (self.len == N) { self.cut = true; return false; }
        self.data[self.len] = c as u8;
        self.len += 1;
        return true;
    }
    pushStr &self s:str -> bool {
        unsafe { return self.write(s.ptr, s.len) == s.len; }
    }
    // The last byte, removed; nothing if the string is empty.
    pop &self -> Option<char> {
        if (self.len == 0) { return Option.None; }
        self.len -= 1;
        return Option.Some(self.data[self.len] as char);
    }

    // The text as a borrowed view. `unsafe` for the reason `String.view` is: it points into this
    // value, so it dangles once this goes out of scope or is written to. The methods below read
    // the text without handing it out.
    unsafe view &self -> str { return self.data[..self.len] as str; }

    startsWith &self prefix:str -> bool { return strStartsWith(self.data[..self.len] as str, prefix); }
    endsWith   &self suffix:str -> bool { return strEndsWith(self.data[..self.len] as str, suffix); }
    contains   &self needle:str -> bool { return strContains(self.data[..self.len] as str, needle); }
    find       &self needle:str -> Option<long> { return strFind(self.data[..self.len] as str, needle); }
    // A String of its own, for when the text must outlive this value or grow past N.
    toString   &self -> String { return stringOf(self.data[..self.len] as str); }
}

// Equal, ordered and hashed by content, like `str` and `String`, so one is a map key and sorts.
// (A struct with an array field gets no derived `==`, and the bytes past `len` are not the text.)
methods FixedString<N> for Eq<str> {
    eq &self other:str -> bool { return strEq(self.data[..self.len] as str, other); }
}
methods FixedString<N> for Eq<FixedString<N>> {
    eq &self other:FixedString<N> -> bool { return strEq(self.data[..self.len] as str, other.data[..other.len] as str); }
}
methods FixedString<N> for Ord {
    cmp &self other:FixedString<N> -> int { return strCmp(self.data[..self.len] as str, other.data[..other.len] as str); }
}
methods FixedString<N> for Hash {
    hash &self -> u64 { return strHash(self.data[..self.len] as str) as u64; }
}

// `format`, into N bytes inline. N comes from where the result is stored.
pub formatFixed<N: long> fmt:str rest:...any -> FixedString<N> {
    s: FixedString<N>;
    writeArgs(s, fmt, rest);
    return s;
}
// `s`, or as much of it as fits.
pub fixedOf<N: long> s:str -> FixedString<N> {
    f: FixedString<N>;
    f.pushStr(s);
    return f;
}
