// The traits the compiler recognizes by name and wires into language mechanics: it emits calls
// to these that nobody wrote. Every other trait is an ordinary interface. See docs/traits.md.

// Released at scope exit, in reverse declaration order. Implementing it makes a type move-only.
pub trait Drop  { drop &self -> void; }

// The explicit way to duplicate a move-only value. Derived field-wise unless hand-written.
pub trait Clone { clone &self -> Self; }

// Marker for freely duplicable values, derived by the compiler — never implemented by hand.
// As a bound it gates APIs that bitwise-copy a value out of shared storage (Box.get, Vec.get,
// Mutex.get): copying a Drop value that way would double-release its resource.
pub trait Copy { }

// Marker: a statement that computes a value of this type and discards it is a compile error.
// `Result` is its first user — "you have to look at this" is the one half of an error type a
// library cannot enforce for itself.
pub trait MustUse { }

// Zero-arg construction. `x: T;` with no initializer becomes `x = T.new()` — locals at the
// declaration, globals at main's start.
pub trait Default { new -> Self; }

// The output sink: where formatted bytes go. Returns the count written, or a negative errno.
// Lives here rather than write.k because `Display` names it. Leaves: `File` (owning) and
// `FileOut` (borrowed); the BufWriter and StringWriter decorators are in write.k, LockWriter in
// sync.k. A raw (ptr, len) pair rather than a `[u8]`, so calling `write` takes `unsafe`; the
// safe ways in are `fmt.putStr` and `File.writeBytes`.
pub trait Write { write &self ptr:long len:long -> long; }

// The input source. Fills the caller's buffer and returns the count read: 0 = end of input,
// negative = -errno.
pub trait Read { read &self ptr:long len:long -> long; }

// How a value renders under `{}`. The impl writes itself into the sink the formatter hands it
// (via writeTo/put*), never into global stdout — print takes a lock this would re-enter.
pub trait Display { display &self w:Write -> void; }

// What `==` and `!=` mean for a type the hardware cannot compare. The parameter is the
// RIGHT-hand type, not `Self`, so `a == b` looks for `Eq<typeof(b)>` on `typeof(a)` and a type
// may implement it several times at different right-hand types — `String` against both a `str`
// and a `String`. A struct whose fields are all comparable gets it derived on demand.
pub trait Eq<R> { eq &self other:R -> bool; }

// `a + b` on a type of your own. The left operand is taken BY VALUE, not borrowed: that is what
// lets an implementation append in place and hand the same buffer back, so `a + b + c` grows one
// allocation instead of building — and leaking — a new value at every step. It also means `a` is
// moved, which the move checker already reports if you use it afterwards.
//
// Generic over the RIGHT operand, like `Eq`, so a type can be added to several things: `String`
// takes both a `str` and another `String`.
pub trait Add<R> { add self other:R -> Self; }

// The rest of the arithmetic, on Add's terms exactly: the left operand by value so an
// implementation may reuse its storage, generic over the right so one type can answer for several.
// The method is the trait's name in lower case, which is how the checker finds it without a second
// table naming them.
//
// Each of these was a silent hole before it had a trait. An aggregate flows as a pointer, so
// `a - b` on two structs subtracted the two addresses and read the difference back as the struct
// type: no error anywhere, and an answer that moved with the frame layout.
pub trait Sub<R> { sub self other:R -> Self; }
pub trait Mul<R> { mul self other:R -> Self; }
pub trait Div<R> { div self other:R -> Self; }
pub trait Rem<R> { rem self other:R -> Self; }

// The bitwise operators and the shifts, on the same terms. A shift is generic over its right
// operand like the rest, which is what lets `Self << long` be the usual shape without a rule of
// its own. Unusual for a struct to want these, but leaving them the machine operation meant
// `a & b` silently masked two addresses together, so each has a contract to answer to instead.
pub trait BitAnd<R> { bitand self other:R -> Self; }
pub trait BitOr<R>  { bitor  self other:R -> Self; }
pub trait BitXor<R> { bitxor self other:R -> Self; }
pub trait Shl<R>    { shl    self other:R -> Self; }
pub trait Shr<R>    { shr    self other:R -> Self; }

// `~a`. No type parameter: there is one complement of a value, so the method is named off the type
// alone the way `Ord`'s `cmp` is. `!a` has no trait and never will: it asks whether a truth value
// is false, and a block of bytes has none, so it is refused on an aggregate rather than answered.
pub trait Not { not self -> Self; }

// What `for x in v` walks: a type that can lend its elements as one contiguous slice.
pub trait AsSlice<T> { asSlice &self -> [T]; }

// What `?` asks of a value: does it stop here (`isBreak`), and then what the function hands back
// (`residual`, rebuilt as the caller's own type by `fromResidual`), or else what it goes on with
// (`output`). `T` is the value that goes on, `R` what stops.
pub trait Try<T, R> {
    isBreak &self -> bool;
    output self -> T;
    residual self -> R;
    fromResidual r:R -> Self;
}

// The operations the compiler answers itself. `syscall` is the kernel call (number, then up to six
// arguments); `atCompileTime` says whether the code is running in the compile-time evaluator,
// which has no `asm`; `exit` runs the `@fini` hooks and ends the process.
pub unsafe builtin syscall nr:long args:...long -> long;
pub builtin atCompileTime -> bool;
pub builtin exit status:long -> never;

// `v[i]` and `v[i] = x` on a type of your own, the same way `==` is `Eq::eq`. Two parameters
// rather than one: `I` is what you index BY and `T` what comes back, and with no associated
// types the second has nowhere else to live. A type may implement either at several key types
// — the argument settles which is meant, exactly as it does for `Eq`.
//
// Reading and writing are separate traits because they are separately possible: a view can
// answer `at` without being writable, and neither is derivable, since only the container knows
// what an index means.
//
// `at` hands out a BORROW of the element, so a container of owning elements implements it like
// any other: the element is read, written or lent in place, and `setAt` takes the new value as a
// `sink` and releases what the slot held.
pub trait Index<I, T>    { at    &self i:I -> &T; }
pub trait IndexSet<I, T> { setAt &self i:I v:sink T -> void; }

// What a closure implements, and what `f(x)` calls on any value implementing it, is `FnN` for the
// arity N. They are not declared here, and there is no list of them anywhere: a trait cannot be
// variadic in its type parameters, so one per arity is unavoidable, but the compiler makes the one
// it needs when it meets it (`Parser::fnTraitFor`). `Fn(A, B) -> R` is how a bound or a type spells
// `Fn2<A, B, R>`, and `Fn(sink A) -> R` a parameter the call gives away. Any arity works.
