// Interned strings: turn a name into a small integer once, and compare integers thereafter.
//
//     names: Interner;
//     a: long = names.intern("count");
//     b: long = names.intern("count");        // a == b, and the compare was one instruction
//     println("{}", names.nameOf(a));         // "count"
//
// This is what a compiler, a parser, a symbol table or anything else that meets the same names
// over and over wants instead of a `String` per occurrence: an id is `Copy`, so it can be a map
// key, an enum payload or a struct field without owning anything and without dangling.
//
// The bytes live in `owned` and are never removed — interning is monotone, which is the whole
// bargain: an id stays valid for the life of the interner, so nothing has to be re-checked.
// `views` is a parallel vector of `str` into them, which is what makes `nameOf` free: a `str` is
// Copy, so it is handed back rather than cloned. A view stays valid as `owned` grows because a
// `String`'s bytes are its own heap block — growth moves the 24-byte headers, not the text.
#include <{string, vec, map, option}>

pub struct Interner {
    owned:  Vec<String>,
    views:  Vec<str>,
    byName: HashMap<str, long>
}

methods Interner for Default {
    new -> Interner {
        o: Vec<String>; v: Vec<str>; m: HashMap<str, long>;
        return Interner { owned: o, views: v, byName: m };
    }
}

methods Interner {
    // The id for `s`, the same one every time. Interning a name already held costs a lookup and
    // no allocation.
    intern &self s:str -> long {
        hit: Option<long> = self.byName.find(s);
        match hit { Some(id) { return id; } None { } }
        held: String = stringOf(s);
        view: str = "";
        unsafe { view = held.view(); }   // pushing moves the header; these bytes stay put
        self.owned.push(held);
        self.views.push(view);
        id: long = self.views.len() - 1;
        self.byName.put(view, id);
        return id;
    }

    // The text an id stands for. An id this interner never issued answers `<none>` rather than
    // trapping, because the usual caller is a diagnostic and a wrong id should not become a
    // second failure on top of the one being reported.
    nameOf &self id:long -> str {
        if (id < 0 || id >= self.views.len()) { return "<none>"; }
        return self.views.get(id);
    }

    // Intern `s` and hand back the interner's OWN copy of it: a `str` that outlives whatever
    // buffer the text came from. The way to keep a slice of a file, a token or an argument
    // without owning a `String` for each one.
    keep &self s:str -> str { return self.nameOf(self.intern(s)); }

    // The same two, for text that was BUILT rather than borrowed. `String.view` is `unsafe`
    // because the view dangles if the String is dropped or grown while it is held — but
    // interning copies the bytes immediately, so that cannot happen here. Taking the String
    // means the caller never opens an `unsafe` block of its own, which is what makes
    // "assemble a name, then intern it" an ordinary two-line thing to write.
    internString &self s:String -> long { unsafe { return self.intern(s.view()); } }
    keepString   &self s:String -> str  { unsafe { return self.keep(s.view()); } }

    count &self -> long { return self.views.len(); }
    // The id `s` already has, without giving it one if it has none.
    lookup &self s:str -> Option<long> { return self.byName.find(s); }
    has &self s:str -> bool { return self.byName.has(s); }
}
