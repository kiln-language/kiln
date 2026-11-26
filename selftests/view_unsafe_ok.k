// A view a local takes inside `unsafe` holds nothing: the block vouches for it. `keepAll` moves a
// String into a Vec after taking its view, which keeps the bytes where they are (a String's text
// lives in its own heap block), and keeps the view beside it, as the interner does. Exits 42.
#include <stdlib::{io, vec, string, intern}>

keepAll inout owned:Vec<String> inout views:Vec<str> s:str -> void {
    held: String = stringOf(s);
    view: str = "";
    unsafe { view = held.view(); }
    owned.push(held);
    views.push(view);
}

main -> int {
    owned: Vec<String>;
    views: Vec<str>;
    keepAll(&owned, &views, "kept");
    names: Interner = Interner.new();
    a: long = names.intern("count");
    b: long = names.intern("count");
    if (views.get(0) == "kept" && a == b && names.nameOf(a) == "count") { return 42; }
    return 1;
}
