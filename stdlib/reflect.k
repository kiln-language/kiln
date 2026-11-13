// A type's declaration as a value: what a derive macro reads.
//
// A trait may name a macro that writes its implementation for any type that lacks one --
// `trait Encode derive deriveEncode { ... }` -- and when the program needs that implementation
// the compiler builds one of these from its own tables and hands it to the macro as its one
// parameter: a `Struct`, an `Enum`, or a `Decl` for a macro that takes either. The macro
// returns `quote { methods @(t.name) for Encode { ... } }`, which is checked like hand-written
// code; or it calls `refuse(why)`, and the compile stops with `why` where the implementation
// was needed. Nothing here costs anything at runtime: a program that builds one by hand has
// built an ordinary value.
//
// The compiler fills these by FIELD NAME, each field only if it is declared here, so a field can
// be added without the compiler having to know; the ones it fills are the ones below. A type
// is named as the compiler holds it: qualified (`shapes::Point`), a generic type's instance by
// its stamped name (`Pair_long_string::String`, its fields at their concrete types), and a
// field's type spelled the way a quote may splice it where a type is read (`long`,
// `shapes::Point`, `ptr_u8` for `*u8`, `slice_u8` for `[u8]`).
#include <{vec, panic, string, sys}>

// One field of a struct, or one value a variant carries.
pub struct Field {
    name: str,             // as declared; for a variant's payload, the slot it is laid out in
                           // (`$Circle$0`), which a quote's `self.@(f.name)` reads in place
    typeName: str,         // the type, spelled as above
    isRawPointer: bool,    // `*T`: an address, meaningless outside this process
    isFn: bool,            // a function pointer: likewise
    isTraitObject: bool,   // a trait object: its concrete type is not known here
    isArray: bool,         // an inline `[T; count]`; `typeName` is the element's
    count: long
}

pub struct Struct { name: str, fields: Vec<Field> }

// One variant: its name, the integer it is (a sum type's tag, or a backed enum's value), and
// the values it carries, in order.
pub struct Variant { name: str, tag: long, payloads: Vec<Field> }

pub struct Enum {
    name: str,
    isBacked: bool,        // `enum E: long { ... }`: a set of named integers, no payloads, no tag field
    backing: str,          // the integer type it is (`int` unless declared)
    tagField: str,         // a sum type's tag, read in place as `self.@(e.tagField)`; "" if backed
    variants: Vec<Variant>
}

// For a derive macro that takes either.
pub enum Decl { OfStruct(Struct), OfEnum(Enum) }

// A derive macro declining the type it was handed: the compile stops with `why`, naming the
// type, the trait and the function that needed the implementation. (The compiler answers this
// call itself while a macro runs; reached at runtime it is a panic.) A `String`, since the reason
// is nearly always `format(...)`; a fixed one is `stringOf("...")`.
pub refuse why:String -> never { unsafe { sysWrite(2, why.view().ptr, why.len()); } sysExit(1); }
