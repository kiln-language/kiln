// What the type names mean, and what converts to what.
//
// Per type: how many bytes it occupies, where it sits on the numeric widening ladder, whether it
// is an aggregate, and whether it carries a companion name (a struct's name, a slice's element).
#include <ast>
#include <support::compiler>
#include <stdlib::{chars, map, option, string, fmt}>

// One row per type. `precedence` is the numeric widening rank: 0 means "not on the ladder", so
// two operands of different rank widen to the higher. `named` marks the types whose meaning is
// incomplete without their companion name. `bare` marks the ones a program can write by name, so
// `scalarNamed` can be built from these rows instead of repeating their spellings.
pub struct TypeInfo { size: long, precedence: long, name: str, aggregate: bool, named: bool, unsignedNum: bool, bare: bool }

// One row per `Lit`, keyed by the tag. `typeInfo` is asked by `isAggregate`,
// `isUnsignedInt`, `higherPrecedence` and `canImplicitlyConvert`, which is several times
// per expression node.
//
// Like `gScalarNames` below, this is data computed when the compiler itself is built.
local gTypeRows: HashMap<long, TypeInfo> = map![
    Lit.Int      as long => TypeInfo { size: 4, precedence: 2, name: "int", aggregate: false, named: false, unsignedNum: false, bare: true },
    Lit.Long     as long => TypeInfo { size: 8, precedence: 3, name: "long", aggregate: false, named: false, unsignedNum: false, bare: true },
    Lit.Char     as long => TypeInfo { size: 1, precedence: 1, name: "char", aggregate: false, named: false, unsignedNum: false, bare: true },
    Lit.Float    as long => TypeInfo { size: 4, precedence: 4, name: "f32", aggregate: false, named: false, unsignedNum: false, bare: true },
    Lit.Double   as long => TypeInfo { size: 8, precedence: 5, name: "f64", aggregate: false, named: false, unsignedNum: false, bare: true },
    Lit.Str      as long => TypeInfo { size: 16, precedence: 0, name: "str", aggregate: true, named: false, unsignedNum: false, bare: true },
    Lit.Slice    as long => TypeInfo { size: 16, precedence: 0, name: "slice", aggregate: true, named: true, unsignedNum: false, bare: false },
    Lit.Any      as long => TypeInfo { size: 24, precedence: 0, name: "any", aggregate: true, named: false, unsignedNum: false, bare: true },
    Lit.Tuple    as long => TypeInfo { size: 0, precedence: 0, name: "tuple", aggregate: true, named: false, unsignedNum: false, bare: false },
    Lit.Struct   as long => TypeInfo { size: 0, precedence: 0, name: "struct", aggregate: true, named: true, unsignedNum: false, bare: false },
    Lit.TraitObj as long => TypeInfo { size: 16, precedence: 0, name: "trait", aggregate: true, named: true, unsignedNum: false, bare: false },
    Lit.TypeVar  as long => TypeInfo { size: 8, precedence: 0, name: "typevar", aggregate: false, named: true, unsignedNum: false, bare: false },
    Lit.Ref      as long => TypeInfo { size: 8, precedence: 0, name: "ref", aggregate: false, named: true, unsignedNum: false, bare: false },
    Lit.Fn       as long => TypeInfo { size: 8, precedence: 0, name: "fn", aggregate: false, named: true, unsignedNum: false, bare: false },
    Lit.I16      as long => TypeInfo { size: 2, precedence: 1, name: "i16", aggregate: false, named: false, unsignedNum: false, bare: true },
    Lit.U8       as long => TypeInfo { size: 1, precedence: 1, name: "u8", aggregate: false, named: false, unsignedNum: true, bare: true },
    Lit.U16      as long => TypeInfo { size: 2, precedence: 1, name: "u16", aggregate: false, named: false, unsignedNum: true, bare: true },
    Lit.U32      as long => TypeInfo { size: 4, precedence: 2, name: "u32", aggregate: false, named: false, unsignedNum: true, bare: true },
    Lit.U64      as long => TypeInfo { size: 8, precedence: 3, name: "u64", aggregate: false, named: false, unsignedNum: true, bare: true },
    Lit.Bool     as long => TypeInfo { size: 1, precedence: 1, name: "bool", aggregate: false, named: false, unsignedNum: true, bare: true },
    Lit.Ptr      as long => TypeInfo { size: 8, precedence: 0, name: "ptr", aggregate: false, named: true, unsignedNum: false, bare: false },
    Lit.Void     as long => TypeInfo { size: 0, precedence: 0, name: "void", aggregate: false, named: false, unsignedNum: false, bare: true },
    Lit.Len      as long => TypeInfo { size: 0, precedence: 0, name: "length", aggregate: false, named: true, unsignedNum: false, bare: false },
];

// A tag with no row of its own reads as `void`. The map stays the one place a row is written, but
// what is asked at run time is `gTypeDense`: the same rows in an array indexed by tag, built from
// the map when this compiler is compiled. A hash probe per question cost a fifth of the
// compile-time evaluator's time running a loop (every load and store asks for a width), and a
// share of every pass.
local rowOf t:Lit -> TypeInfo {
    hit: Option<TypeInfo> = gTypeRows.find(t as long);
    match hit { Some(v) { return v; } None { } }
    return gTypeRows.get(Lit.Void as long);
}
local gTypeDense: Vec<TypeInfo> = buildTypeDense();
local buildTypeDense -> Vec<TypeInfo> {
    v: Vec<TypeInfo>;
    i: long = 0;
    while (!strEq(nameof(Lit, i as Lit), "?")) { v.push(rowOf(i as Lit)); i = i + 1; }
    return v;
}
pub typeInfo t:Lit -> TypeInfo {
    i: long = t as long;
    if (i >= 0 && i < gTypeDense.len()) { return gTypeDense.get(i); }
    return gTypeDense.get(Lit.Void as long);
}

pub typeName t:Lit -> str { return typeInfo(t).name; }
pub isUnsignedInt t:Lit -> bool { return typeInfo(t).unsignedNum; }
pub isAggregate t:Lit -> bool { return typeInfo(t).aggregate; }

// The type a name spells, or `Lit.Void` if it names no scalar.
//
// It is built from the rows above rather than repeating them. A type's canonical spelling is
// `TypeInfo.name`; a second copy here would have to be renamed in step with it, or the parser
// would go on accepting a name the diagnostics no longer print. What is added by hand is only the
// aliases, the spellings no row carries: `i8`/`i32`/`i64` for signed widths that already have
// names, and `byte`/`usize` for unsigned ones. Only a genuinely new width gets a row.
//
// One table answers both questions, and it is computed when this compiler is compiled. `void` is
// in it so that a name spelled `void` can be told apart from one that names nothing, which is the
// whole difference between `scalarNamed` and `namesScalar`.
local gScalarNames: HashMap<str, long> = buildScalarNames();

local buildScalarNames -> HashMap<str, long> {
    m: HashMap<str, long>;
    i: long = 0;
    while (!strEq(nameof(Lit, i as Lit), "?")) {
        row: TypeInfo = typeInfo(i as Lit);
        if (row.bare) { m.put(row.name, i); }
        i = i + 1;
    }
    m.put("i32", Lit.Int as long);
    m.put("i64", Lit.Long as long);
    m.put("i8", Lit.Char as long);
    m.put("byte", Lit.U8 as long);
    m.put("usize", Lit.U64 as long);
    // The C names for the two IEEE-754 widths, beside the sized ones the rows carry.
    m.put("float", Lit.Float as long);
    m.put("double", Lit.Double as long);
    return m;
}

pub scalarNamed n:str -> Lit {
    hit: Option<long> = gScalarNames.find(n);
    match hit { Some(v) { return v as Lit; } None { } }
    return Lit.Void;
}
pub namesScalar n:str -> bool {
    return gScalarNames.has(n);
}

// A scalar a `methods T for Trait` block may be written for. `any`, a slice and `void` are
// shapes rather than types with values of their own: an impl for one could not say which type it
// was implementing for, so a bound would have nothing to resolve to.
pub isImplableScalar t:Lit -> bool {
    return t == Lit.Char || t == Lit.I16 || t == Lit.Int || t == Lit.Long
        || t == Lit.U8 || t == Lit.U16 || t == Lit.U32 || t == Lit.U64
        || t == Lit.Bool || t == Lit.Float || t == Lit.Double || t == Lit.Str;
}

pub isFloat t:Lit -> bool { return t == Lit.Float || t == Lit.Double; }

pub isInteger t:Lit -> bool {
    return t == Lit.Char || t == Lit.I16 || t == Lit.Int || t == Lit.Long
        || t == Lit.U8 || t == Lit.U16 || t == Lit.U32 || t == Lit.U64;
}

// Only lossless widening is implicit; everything else needs an explicit `as`.
//   integer -> wider signed integer      lossless, always
//   unsigned -> wider unsigned integer   lossless
//   signed -> same-width unsigned, or any narrowing: not implicit, write `x as u32`
pub canImplicitlyConvert from:Lit to:Lit -> bool {
    if (from == to) { return true; }
    // Pointers and `long` are interchangeable 8-byte addresses: `&x` initializes a `*T`, and a
    // `*T` passes where a raw address is wanted.
    if ((from == Lit.Ptr || from == Lit.Long) && (to == Lit.Ptr || to == Lit.Long)) { return true; }
    // bool is a 0/1 integer for widening, and any integer is truthy as a bool, so a comparison
    // (which yields 0/1) flows into a bool condition or return.
    if (from == Lit.Bool && isInteger(to)) { return true; }
    if (to == Lit.Bool && isInteger(from)) { return true; }
    if (isInteger(from) && isInteger(to)) {
        fs: long = typeInfo(from).size;
        ts: long = typeInfo(to).size;
        if (ts <= fs) { return false; }                       // narrowing or same width: explicit
        if (!typeInfo(to).unsignedNum) { return true; }       // strictly wider signed: lossless
        return typeInfo(from).unsignedNum;                    // unsigned -> wider unsigned
    }
    // A float meets anything else, the other float width included, only through `as`: every one
    // of those conversions rounds or truncates somewhere, and none of them should happen unseen.
    return false;
}

// Whether an integer of type `from`, stored into a place of type `to`, has to be narrowed to
// become one of `to`'s values. It does when it does not widen into `to` losslessly and `to` is
// narrower than a word (at eight bytes, the canonical word already is the value). A store to
// memory narrows by its width anyway; a place held in a register (or in an `i64` LLVM slot) needs
// the conversion emitted.
pub narrowsInto from:Lit to:Lit -> bool {
    if (from == to || !isInteger(from) || !isInteger(to)) { return false; }
    if (typeInfo(to).size >= 8) { return false; }
    return !canImplicitlyConvert(from, to);
}

// The two operands of an arithmetic operator or a comparison meet at one type, which the operation
// is computed (and wraps) at. Two integers meet where the widening rule says: at the one the other
// widens to losslessly (`u8 + u16` is a `u16`, `u32 + long` a `long`), or, when neither holds the
// other, at the narrowest signed type that holds both (`u8 + c` with `c: char` is an `i16`,
// `char + u16` and `u16 + i16` are `int`, `u32 + int` is `long`). That way a mix computes the
// value it means, and a comparison orders by that value. A `u64` and a signed type have no such
// type (`noCommonType`), so the checker refuses the operation; what this returns for that pair
// (the higher rank, or the left on a tie) only matters for code the compiler writes itself. Off
// the ladder (rank 0) the left type stands, which is what lets an aggregate operand keep its own
// identity. A literal operand has already taken the other's type before this is asked
// (`Checker.adoptLiteral`).
pub higherPrecedence a:Lit b:Lit -> Lit {
    if (a != b && isInteger(a) && isInteger(b)) {
        if (canImplicitlyConvert(a, b)) { return b; }
        if (canImplicitlyConvert(b, a)) { return a; }
        wide: long = typeInfo(a).size;
        if (typeInfo(b).size > wide) { wide = typeInfo(b).size; }
        if (wide < 2) { return Lit.I16; }
        if (wide < 4) { return Lit.Int; }
        if (wide < 8) { return Lit.Long; }
    }
    if (typeInfo(b).precedence > typeInfo(a).precedence) { return b; }
    return a;
}

// Two integers no integer type holds both of: a `u64` and a signed type. An operation between
// them is refused until one side says with `as` which it means.
pub noCommonType a:Lit b:Lit -> bool {
    if (a == b || !isInteger(a) || !isInteger(b)) { return false; }
    if (canImplicitlyConvert(a, b) || canImplicitlyConvert(b, a)) { return false; }
    return typeInfo(a).size >= 8 || typeInfo(b).size >= 8;
}

// A slice's element identity, used as the slice's companion name so `[char]` and `[int]` are
// different types. It is the element's mangled spelling, which `unmangledType` reads back; a bare
// companion name would make `[*u8]` a slice of bytes and `[fn(long)->long]` a slice of a struct.
pub sliceElemName elemKind:Lit elemStruct:Sym -> str {
    return typeMangleName(elemKind, elemStruct);
}

// How a type is spelled inside a mangled name: a monomorphized instance, a vtable label, a
// trait-object companion. Only a named aggregate contributes its own name; everything else
// contributes its kind, because two instantiations that differ only in kind must not collide.
// `Vec<*u8>` spelled as `Vec_u8` would be `Vec<u8>`, and `Iter<&Res>` is not `Iter<Res>`, so a
// pointer, a slice and a borrow each say what they are.
//
// A type variable is spelled by its own name. Substitution is keyed on the spelling, so `T` has to
// come back as `T` for a pattern's name to be rebuilt under a binding.
pub typeMangleName k:Lit n:Sym -> str {
    if (n == NO_SYM) { return typeName(k); }
    // A length argument is its value: `Buf<64>` is `Buf_64`, however the 64 was spelled.
    if (k == Lit.Struct || k == Lit.TraitObj || k == Lit.TypeVar || k == Lit.Len) { return nameOf(n); }
    if (k == Lit.Ref) { return keepString(format("ref_{}", nameOf(n))); }
    if (k == Lit.Ptr) { return keepString(format("ptr_{}", nameOf(n))); }
    if (k == Lit.Slice) { return keepString(format("slice_{}", nameOf(n))); }
    // A function pointer is spelled by its whole signature (`each<long, fn(long)->void>` names
    // one instance and `each<long, fn(sink long)->void>` another) so the companion, which is a
    // key into the signature table, is what contributes. That key is punctuated text and a symbol
    // is not, so anything but a letter or a digit becomes `_`; a returned borrow's `&` becomes
    // `r`, `ref_` being how a borrow is spelled everywhere else here.
    if (k == Lit.Fn) {
        s: String;
        s.pushStr("fn");
        sig: str = nameOf(n);
        for i in 0..sig.len {
            c: long = charAt(sig, i);
            if (isAlnum(c))    { s.push(c as char); }
            else if (c == '&') { s.push('r'); }
            else               { s.push('_'); }
        }
        out: str = keepString(s);
        if (!gFnMangled.has(out)) { gFnMangled.put(out, n); }
        return out;
    }
    return typeName(k);
}

// Each fn type's mangled spelling, back to its signature key. A fn type that a pointer, a
// borrow or a slice points at, or that a type parameter stands for (`*T` in `Vec<fn(long)->long>`),
// travels as that spelling, and `unmangledType` has to read a fn type back out of it.
pub var gFnMangled: HashMap<str, Sym> = map![];

// ─── how a type is written in source ─────────────────────────────────────────

// A parsed type: the kind, and the companion name when the kind needs one.
pub struct TypeRef { base: Lit, name: Sym }

pub typeRefOf k:Lit -> TypeRef { return TypeRef { base: k, name: NO_SYM }; }
pub namedTypeRef k:Lit n:Sym -> TypeRef { return TypeRef { base: k, name: n }; }


// An `inout x:long` parameter is a pointer to the caller's scalar, typed `&$inout_long`. That is a
// borrow of something no struct table holds, so nothing mistakes it for the `&self` of a `long`
// method. Every use of `x` in the body is `*x`, a lent place (`lentPlaceOf`).
pub INOUT_SCALAR: str = "$inout_";
pub isInoutScalarName n:Sym -> bool { return n != NO_SYM && strStartsWith(nameOf(n), INOUT_SCALAR); }
pub inoutScalarName k:Lit n:Sym -> Sym { return internString(format("{}{}", INOUT_SCALAR, typeMangleName(k, n))); }
pub inoutScalarOf n:Sym -> TypeRef {
    s: str = nameOf(n);
    return unmangledType(strSlice(s, INOUT_SCALAR.len, s.len - INOUT_SCALAR.len));
}

// `typeMangleName` read backwards: the type a companion name spells. A `*T`, a `[T]` and a `&T`
// each record their referent as the spelling the mangler produced, so `**Node` is a `Ptr` whose
// companion is the text `ptr_Node`, and the only way back to "a pointer to Node" is to take that
// prefix off again. Without this, `rows[0]` of a `**Node` would come back as a struct called
// `ptr_Node`, a type nothing declares, so `rows[0][0]` would have no element type at all and
// would fall through to `long`.
//
// A declared name is always `module::Name`, so no real struct's spelling begins with one of these
// prefixes; a monomorphized instance carries them in the middle (`Vec_ptr_Node`), never in front.
pub unmangledType n:str -> TypeRef {
    if (strStartsWith(n, "ptr_"))   { return TypeRef { base: Lit.Ptr,   name: intern(strSlice(n, 4, n.len - 4)) }; }
    if (strStartsWith(n, "ref_"))   { return TypeRef { base: Lit.Ref,   name: intern(strSlice(n, 4, n.len - 4)) }; }
    if (strStartsWith(n, "slice_")) { return TypeRef { base: Lit.Slice, name: intern(strSlice(n, 6, n.len - 6)) }; }
    if (namesScalar(n)) { return TypeRef { base: scalarNamed(n), name: NO_SYM }; }
    if (strStartsWith(n, "fnfn")) {
        hit: Option<Sym> = gFnMangled.find(n);
        match hit { Some(key) { return TypeRef { base: Lit.Fn, name: key }; } None { } }
    }
    return TypeRef { base: Lit.Struct, name: intern(n) };
}

// A length as a template argument (see `Lit.Len`), and back.
pub lengthArg v:long -> TypeRef {
    s: String;
    s.pushLong(v);
    return TypeRef { base: Lit.Len, name: internString(s) };
}
pub lengthValue t:TypeRef -> long {
    v: Option<long> = parseLong(nameOf(t.name));
    match v { Some(n) { return n; } None { } }
    return 0;
}

// Whether an untyped literal's value is one the declared width can hold. A literal takes the
// type it is handed, which is what makes `f(3)` into a `u8` parameter a 3 rather than a narrowing
// the author has to write out, but only when the value really is one of that type's.
// `c: char = 300` is not: no `char` holds 300, and the store would write 44. A negative literal
// fits no unsigned type, `u64` included. A literal written past `long`'s maximum is a `u64`
// literal (its bits are in `v`, so it reads as negative) and is checked apart from this, since
// nothing but a `u64` holds it.
pub literalFits v:long k:Lit -> bool {
    if (!isInteger(k) && k != Lit.Bool) { return true; }
    sz: long = typeInfo(k).size;
    if (sz <= 0) { return true; }
    if (typeInfo(k).unsignedNum && v < 0) { return false; }
    if (sz >= 8) { return true; }                   // a long literal is already a long
    bits: long = sz * 8;
    if (typeInfo(k).unsignedNum) { return v < (1 << bits); }
    half: long = 1 << (bits - 1);
    return v >= (0 - half) && v < half;
}

// The scalars a blanket implementation's category holds (`methods<T: Integer> T for Hash`), in a
// fixed order; none for a name that is not one. `Integer` is every integer type (`char` is `i8`),
// `Signed` and `Unsigned` its two halves, `Float` the two IEEE widths.
pub blanketScalars cat:str -> Vec<Lit> {
    out: Vec<Lit>;
    signed: bool = cat == "Integer" || cat == "Signed";
    unsigned: bool = cat == "Integer" || cat == "Unsigned";
    if (signed) { out.push(Lit.Char); out.push(Lit.I16); out.push(Lit.Int); out.push(Lit.Long); }
    if (unsigned) { out.push(Lit.U8); out.push(Lit.U16); out.push(Lit.U32); out.push(Lit.U64); }
    if (cat == "Float") { out.push(Lit.Float); out.push(Lit.Double); }
    return out;
}
