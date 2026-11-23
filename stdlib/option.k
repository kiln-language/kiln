// `Option<T>`: a T, or nothing. An ordinary sum type; the compiler knows nothing about it.
//
// Being a tagged union it costs the payload plus a tag rather than a T plus a separate flag,
// and the None case never constructs a T, so the payload may own a resource (`Option<File>`).
//
// Anything that hands the payload out takes `self` by value and consumes the option: a copy of
// an owning payload would be a second handle to one resource, released twice. Anything that
// only reads the tag borrows, so you can ask before you take:
//
//     if (o.isSome()) { v: T = o.unwrap(); }
//
// Unlike `Result`, an Option is deliberately not `MustUse`: "there is no value" is often the
// answer you were checking for.
#include <{core, panic, mem}>

pub enum Option<T> {
    None,
    Some(T)
}

// What a `None` hands back through `?`: nothing but the fact.
pub struct NoneResidual { }

// What `?` does with an Option: a `None` stops and is handed back as the caller's own None.
methods Option<T> for Try<T, NoneResidual> {
    isBreak &self -> bool {
        match self {
            None { return true; }
            _ { }
        }
        return false;
    }
    output self -> T {
        match self {
            None    { panicState("Option ?", "called on a None value"); }
            Some(v) { return v; }
        }
    }
    residual self -> NoneResidual {
        match self {
            None    { return NoneResidual { }; }
            Some(_) { panicState("Option ?", "called on a Some value"); }
        }
    }
    fromResidual r:NoneResidual -> Option<T> { return Option.None; }
}

methods Option<T> for Default {
    new -> Option<T> { return Option.None; }
}

methods Option<T> {
    isSome &self -> bool {
        match self {
            Some(_) { return true; }
            None    { return false; }
        }
    }
    isNone &self -> bool { return !self.isSome(); }

    // Traps on None. There is no value of an arbitrary T that means "nothing", and a default here
    // would be indistinguishable from a real answer.
    unwrap self -> T {
        match self {
            Some(v) { return v; }
            None    { panicState("Option.unwrap", "called on a None value"); }
        }
    }

    // The same trap, saying what the caller expected instead of naming the call.
    expect self msg:str -> T {
        match self {
            Some(v) { return v; }
            None    { panic(msg); }
        }
    }

    // The total accessor: no trap, no check needed at the call site. `alt` is consumed either
    // way, so an owning fallback is released when it is not needed.
    unwrapOr self alt:T -> T {
        match self {
            Some(v) { return v; }
            None    { return alt; }
        }
    }

    // The payload, leaving None in its place: how a field of type Option<T> is emptied while its
    // owner keeps living.
    take &self -> Option<T> { return replace(self, Option.None); }
}

methods Option<T: Default> {
    // The payload, or T's default.
    unwrapOrDefault self -> T {
        match self {
            Some(v) { return v; }
            None    { return T.new(); }
        }
    }
}

// ─── combinators ─────────────────────────────────────────────────────────────
// Free functions rather than methods: each introduces a type parameter of its own, and a
// `methods` block carries only the type's. All consume, since they take the payload out. Each
// takes its callback by bound, so a closure and a named function are the same call, and the
// call is direct.

// `f` of the payload, if there is one; `f` is not called when there is not. A closure whose
// result type is not otherwise known has to say it (`|x: long| -> long { ... }`).
pub mapOption<T, U, F: Fn(T) -> U> o:Option<T> f:F -> Option<U> {
    match o {
        Some(v) { return Option.Some(f(v)); }
        None    { return Option.None; }
    }
}

// The payload if it satisfies `pred`, nothing otherwise. The predicate borrows the payload, so
// it is still there to be handed back, and a rejected one is released here.
pub filterOption<T, F: Fn(T) -> bool> o:Option<T> pred:F -> Option<T> {
    match o {
        Some(v) { if (pred(v)) { return Option.Some(v); } return Option.None; }
        None    { return Option.None; }
    }
}

// The first of the two that holds a value. Not short-circuiting: `b` is evaluated by the
// caller either way, and if `a` wins, `b` is released here.
pub orOption<T> a:Option<T> b:Option<T> -> Option<T> {
    match a {
        Some(v) { return Option.Some(v); }
        None    { return b; }
    }
}

