// `Result<T, E>` — a value, or the reason there isn't one. An ordinary two-parameter sum type,
// so it costs max(sizeof(T), sizeof(E)) plus a tag and only the live arm is ever built; a
// payload that owns something (`Result<File, long>`) is ordinary.
//
// The one thing it takes from the compiler is `MustUse` (core.k): discarding a Result is a
// compile error, which is the half of an error type no library can enforce for itself.
//
// Accessors follow Option's split — `isOk`/`isErr` borrow, everything that yields a payload
// consumes, since a copy of an owning payload would be released twice:
//
//     if (r.isOk()) { v: T = r.unwrap(); }
#include <{core, panic, option}>

pub enum Result<T, E> {
    Ok(T),
    Err(E)
}

methods Result<T, E> for MustUse { }

// Reaching for the arm that does not exist is a caller bug, so it ends the program — after
// saying which call did it, since the alternative is a SIGILL with nothing attached.
local wrongArm what:str -> never {
    panicState(what, "the result holds the other arm — use isOk, unwrapOr or a match");
}

// What `?` does with a Result: an `Err` stops and is handed back as the caller's own Result.
// `Err` is tested first everywhere, as `isBreak` does, so the second test can fold away.
methods Result<T, E> for Try<T, E> {
    isBreak &self -> bool {
        match self {
            Err(_) { return true; }
            _ { }
        }
        return false;
    }
    output self -> T {
        match self {
            Err(_) { wrongArm("Result ?"); }
            Ok(v)  { return v; }
        }
    }
    residual self -> E {
        match self {
            Err(e) { return e; }
            Ok(_)  { wrongArm("Result ?"); }
        }
    }
    fromResidual e:E -> Result<T, E> { return Result.Err(e); }
}

methods Result<T, E> {
    isOk &self -> bool {
        match self {
            Ok(_)  { return true; }
            Err(_) { return false; }
        }
    }
    isErr &self -> bool { return !self.isOk(); }

    // Traps on the wrong arm. Handing back a default would turn a checked failure back into
    // the unchecked one this type exists to replace.
    unwrap self -> T {
        match self {
            Ok(v)  { return v; }
            Err(_) { wrongArm("Result.unwrap"); }
        }
    }
    // The same trap, saying what the caller expected instead of naming the call.
    expect self msg:str -> T {
        match self {
            Ok(v)  { return v; }
            Err(_) { panic(msg); }
        }
    }

    // The total accessor. `alt` is consumed either way — released here when it is not needed —
    // which is what makes an owning fallback safe to pass.
    unwrapOr self alt:T -> T {
        match self {
            Ok(v)  { return v; }
            Err(_) { return alt; }
        }
    }

    unwrapErr self -> E {
        match self {
            Ok(_)  { wrongArm("Result.unwrapErr"); }
            Err(e) { return e; }
        }
    }

    errorOr self alt:E -> E {
        match self {
            Ok(_)  { return alt; }
            Err(e) { return e; }
        }
    }
}

// ─── transforming one arm ────────────────────────────────────────────────────
// Free functions for the same reason Option's combinators are: each introduces a type of its
// own. The callback is a bound, so a closure or a named function, and it is called only on the
// arm it is for; the other arm passes through untouched.

pub mapResult<T, U, E, F: Fn(T) -> U> r:Result<T, E> f:F -> Result<U, E> {
    match r {
        Ok(v)  { return Result.Ok(f(v)); }
        Err(e) { return Result.Err(e); }
    }
}
pub mapError<T, E, G, F: Fn(E) -> G> r:Result<T, E> f:F -> Result<T, G> {
    match r {
        Ok(v)  { return Result.Ok(v); }
        Err(e) { return Result.Err(f(e)); }
    }
}

// ─── converting to and from Option ──────────────────────────────────────────
// A Result says why there is no value, an Option only that there isn't one, so converting is
// discarding the reason or supplying it. All three consume, like every other accessor.

// The value, discarding the error — including releasing whatever it owned.
pub okOf<T, E> r:Result<T, E> -> Option<T> {
    match r {
        Ok(v)  { return Option.Some(v); }
        Err(_) { return Option.None; }
    }
}

// The error, discarding the value.
pub errOf<T, E> r:Result<T, E> -> Option<E> {
    match r {
        Ok(_)  { return Option.None; }
        Err(e) { return Option.Some(e); }
    }
}

// An Option plus the reason its absence counts as a failure. `E` is inferred from `e`, and a
// bare literal is an `int`, so a `Result<T, long>` needs `okOr(o, 22 as long)` or a typed
// local — unlike `Result.Err(22)`, which is target-typed by what it is returned as.
pub okOr<T, E> o:Option<T> e:E -> Result<T, E> {
    match o {
        Some(v) { return Result.Ok(v); }
        None    { return Result.Err(e); }
    }
}
