// Typed three-address IR.
//
// Every operand is a virtual register (a "temp") and a constant is materialised into one by
// `Const`, so operands are uniform. Each temp carries a type, so the back end derives operand
// widths and extensions from types rather than assuming eight bytes everywhere.
#include <parse::{ast, registry, types}>
#include <support::compiler>
#include <stdlib::{chars, map, option, string, vec}>

pub type Temp = long;
pub NO_TEMP: Temp = -1;

pub enum IROp: int {
    Const,      // dst = imm
    Load,       // dst = <var>
    Store,      // <var> = a
    Mov,        // dst = a

    Add, Sub, Mul, Div, Mod,
    BAnd, BOr, BXor,
    Shl, Shr,                  // Shr is arithmetic. It sign-extends
    BNot,

    CmpEq, CmpNe, CmpLt, CmpGt, CmpLe, CmpGe,   // dst = (a cmp b) ? 1 : 0

    Convert,    // dst = a, from one width to another

    Call,       // dst = <name>(args...)
    Ret,        // return a
    RetVoid,

    Label,      // <name>:
    Jmp,
    Jz,         // if a == 0, jump

    Asm,        // an inline assembly block; clobbers like a call

    ArrLoad,    // dst = <name>[a]
    ArrStore,   // <name>[a] = b
    AddrOf,     // dst = &<name>
    StrAddr,    // dst = the address of a string literal's bytes

    // Aggregates: values larger than one register, which flow as a pointer.
    PtrLoad,    // dst = [a + x*scale + imm]
    PtrStore,   // [a + x*scale + imm] = b
    AggCopy,    // memcpy [a] <- [b], imm bytes
    AggZero,    // memset [a] <- 0, imm bytes: a local array declared without a value
    Bounds,     // trap unless (unsigned) a < b, or a <= b for a slice check; `imm` is the kind
    StrLitVal,  // dst = the address of a 16-byte {ptr, len} constant
    AggSlot,    // dst = the address of hidden aggregate scratch slot #imm
    VtableAddr, // dst = the address of the vtable named <name>
    FnAddr,     // dst = the address of the function named <name>
    CallIndirect,  // dst = (*a)(args...): through a pointer, which is what a vtable slot holds

    // A fused compare-and-branch. The optimizer makes these (`Opt.fuseBranches`), and so does
    // the lowerer, which ends a condition's block with the comparison itself (`branchUnless`),
    // so anything reading the IR straight out of lowering can meet one.
    Jcc,        // if (a <cmpOp> b) jump

    // A deleted instruction. The instruction list is flat across the program and every `IRFunc`
    // names a run in it by index, so removing an entry would move every function after it. A
    // pass blanks one instead, and everything that walks the list skips it: the emitter, the
    // CFG, the allocator. Nothing else ever produces one.
    Nop,

    // `recover { body } else { handler }`. `RecoverPush` fills the record in hidden aggregate
    // slot #imm with where a `raise` resumes (the handler, at label `name`) and the stack and
    // registers it resumes with; the call that links the record follows it as an ordinary call.
    RecoverPush,
    // Ends a block of a `recover` body after each call and `asm` block, which may raise: the
    // handler at label `name` can follow it as well as the next instruction. It emits nothing.
    // It is not a branch: no pass may point it somewhere else, since the handler is entered at
    // the address `RecoverPush` recorded and not by following this edge.
    FaultEdge,

    // An atomic access of the word at address `a`: `imm` is which (one of the eight-byte
    // `BI_ATOMIC_*` kinds), `kind` the word's type (`long` or `int`), `b` the value stored, added
    // or swapped in (the expected one for a compare-and-swap, whose desired value is its one
    // argument), `dst` the value read (the old one, for all but a store). It is never removed,
    // merged or moved, and ends what is known of any memory another thread can reach (`flow.k`).
    Atomic,

    // `memcpy`: from address `b` to address `a`, as many bytes as its one argument says, the two
    // ranges apart. It writes the destination range and nothing else, so that is all it ends
    // (`flow.k`).
    MemCopy
}

// What a `Bounds` check holds, in its `imm`, and so what its report says when it fails. An index
// must be below the length. A slice's bounds may reach it, so the three slice checks are
// inclusive: the end against the length, the start against the end, and the start against the
// length when no end was written.
pub BOUNDS_INDEX: long = 0;          // "index 7 out of range for length 3"
pub BOUNDS_SLICE_END: long = 1;      // "slice end 5 out of range for length 3"
pub BOUNDS_SLICE_ORDER: long = 2;    // "slice start 2 is past slice end 1"
pub BOUNDS_SLICE_START: long = 3;    // "slice start 5 out of range for length 3"

// What a call's callee does with the addresses it is handed, by its declared conventions, in a
// `Call`'s or `CallIndirect`'s `imm` (`Lowerer.callConventions`). CALL_KNOWN when they are known
// and the callee is not declared `unsafe`; then bit k (k < CALL_ARGS) says argument k is an
// address the callee is lent and never keeps (a borrow, an aggregate it copies, a `str`, slice or
// trait object's pair, the result's `$sret`), and bit CALL_ARGS + k that it may write there. In
// safe code a borrow never outlives its call, so a frame slot lent to one call is invisible to
// every other.
pub CALL_KNOWN: long = 4611686018427387904;   // bit 62
pub CALL_ARGS: long = 30;
pub callLends imm:long k:long -> bool { return (imm & CALL_KNOWN) != 0 && k < CALL_ARGS && (imm & (1 << k)) != 0; }
pub callMayWrite imm:long k:long -> bool {
    if ((imm & CALL_KNOWN) == 0 || k >= CALL_ARGS) { return true; }
    return (imm & (1 << (CALL_ARGS + k))) != 0;
}

// A direct `Call`'s arguments that hand the callee bytes nothing reads again (a value built for
// the call, an owning local the call moves: `Lowerer.freshArg`), as a mask by position in the
// call's `scale`, which nothing else reads on a call (only a `PtrLoad` or `PtrStore` has an
// index to scale). A parameter taken by value that every call hands such bytes owns them where
// they lie, without the prologue's copy (`ownMovedArgs`).
pub CALL_FRESH_ALL: long = 4611686018427387903;   // bits 0 to 61

// Another object may call this one's functions (`--lib`) or be called by them (`--use`), so not
// every call to a function is in sight; a package build (`gKlibMode`) has dependents it cannot
// see either. What follows from seeing every call is only drawn where none of these holds.
pub var gOpenObject: bool = false;
// `--no-moved-args`: every struct or tuple taken by value is copied by its callee's prologue,
// moved into the call or not (`ownMovedArgs`).
pub var gMovedArgsOff: bool = false;

// What `flow.k` proved of a signed `Div` or `Mod` by a constant, in its `imm` (zero otherwise):
// the dividend is never negative, so rounding toward zero has nothing to correct and the emitter
// leaves that step out (`emitDivideConst`).
pub DIV_NONNEG: long = 1;

// The two "what does this wreck?" questions, asked by the register allocator and by the passes
// that cache loads. They live beside the opcode list because that is the one place a new opcode
// is certain to be looked at. An op missing from one of them never crashes anything: it quietly
// gives a wrong allocation or a stale cached load, which is why they are kept here.
pub clobbersRegisters op:IROp -> bool {
    return op == IROp.Call || op == IROp.CallIndirect || op == IROp.Asm;
}
// Whether the op may write memory that cannot be named: anything reachable through a pointer.
// `ArrStore` is deliberately absent. It writes one element of a local array, and array slots
// never overlap the named scalar slots the load cache keys on.
pub clobbersMemory op:IROp -> bool {
    return clobbersRegisters(op) || op == IROp.PtrStore || op == IROp.AggCopy || op == IROp.AggZero
        || op == IROp.RecoverPush || op == IROp.Atomic || op == IROp.MemCopy;
}

// An aggregate a callee owns a copy of, rather than a borrow of the caller's. A struct and a
// tuple are values, so the prologue copies them into storage of their own; `str`, a slice and a
// trait object are already pointers to their own pair, and a `Ref` is a borrow by definition.
pub byValueAggregate k:Lit -> bool { return k == Lit.Struct || k == Lit.Tuple; }

// How many bytes a value of this type occupies in memory: 1, 2, 4 or 8. A slot is always eight,
// but the memory a pointer names is the real thing: an array element, a struct field, a byte in a
// buffer.
pub widthOf k:Lit -> long {
    w: long = typeInfo(k).size;
    if (w < 1 || w > 8) { return 8; }
    if (w == 3) { return 4; }
    if (w > 4) { return 8; }
    return w;
}

// Whether `v` is the canonical word of a value of type `k`: what a narrow value is held as in a
// 64-bit register, sign-extended for a signed type and zero-extended for an unsigned one.
pub canonicalIn k:Lit v:long -> bool {
    w: long = widthOf(k);
    if (w >= 8) { return true; }
    bits: long = 8 * w;
    if (typeInfo(k).unsignedNum) { return v >= 0 && v < (1 << bits); }
    return v >= 0 - (1 << (bits - 1)) && v < (1 << (bits - 1));
}


pub isCompare op:IROp -> bool {
    return op == IROp.CmpEq || op == IROp.CmpNe || op == IROp.CmpLt
        || op == IROp.CmpGt || op == IROp.CmpLe || op == IROp.CmpGe;
}

// The comparison that holds of `b, a` exactly when this one holds of `a, b`.
pub swapCompare op:IROp -> IROp {
    if (op == IROp.CmpLt) { return IROp.CmpGt; }
    if (op == IROp.CmpGt) { return IROp.CmpLt; }
    if (op == IROp.CmpLe) { return IROp.CmpGe; }
    if (op == IROp.CmpGe) { return IROp.CmpLe; }
    return op;
}

// The comparison that is true exactly when this one is false. What a `Jz` on a comparison means,
// and what lets a condition be lowered as a jump to the place it does not hold.
pub negateCompare op:IROp -> IROp {
    if (op == IROp.CmpEq) { return IROp.CmpNe; }
    if (op == IROp.CmpNe) { return IROp.CmpEq; }
    if (op == IROp.CmpLt) { return IROp.CmpGe; }
    if (op == IROp.CmpGe) { return IROp.CmpLt; }
    if (op == IROp.CmpGt) { return IROp.CmpLe; }
    return IROp.CmpGt;                       // CmpLe
}

pub isBranch op:IROp -> bool {
    return op == IROp.Jmp || op == IROp.Jz || op == IROp.Jcc;
}
pub isTerminator op:IROp -> bool {
    return isBranch(op) || op == IROp.Ret || op == IROp.RetVoid || op == IROp.FaultEdge;
}

// The size of a `recover` record, whose layout `stdlib::recover` describes: the record it
// replaced, the resume address, rsp, rbp, r12 to r15, and the low eight bytes of xmm12 to xmm14.
pub RECORD_BYTES: long = 88;
pub RECORD_RESUME: long = 8;
pub RECORD_RSP: long = 16;
pub RECORD_RBP: long = 24;
pub RECORD_GPRS: long = 32;
pub RECORD_XMMS: long = 64;

pub struct Instr {
    op:   IROp,
    dst:  Temp,
    a:    Temp,
    b:    Temp,
    imm:  long,

    // Operand `b` as a literal rather than a temp. Set only where the instruction genuinely
    // encodes an immediate, and `b` is cleared to NO_TEMP when it is, so the allocator stops
    // seeing a use and the `Const` that fed it becomes dead.
    bIsImm: bool,
    bImm:   long,

    // A `Load` that is the entry seed for a promoted parameter, whose value is still in its
    // argument register when the function starts. It stays in the IR because it is the temp's
    // definition: deleting it would leave the allocator with a range starting at the first use,
    // free to put something else in that register.
    paramSeed: bool,

    // A `paramSeed` load whose variable `Opt.promoteLocals` promoted. The prologue moves the
    // argument straight into the temp's register (one parallel move over every parameter, since
    // a temp may be given a register another argument arrives in) and the variable's slot is
    // never used. A seed that is not promoted puts the argument in the slot, which the body reads
    // by name. Either way the seed itself is never emitted.
    promoted: bool,

    // A `Call` to a function that never returns (`panicIndex`, `sysExit`, anything the checker
    // found always ends in one). No path leaves it, so a block ends there with no successor,
    // which is what lets a bounds check's facts survive past its panic.
    noReturn: bool,

    cmpOp: IROp,        // Jcc only: which comparison to branch on
    name:  Sym,         // variable, function, or label
    structName: Sym,    // the aggregate `kind` names, when it names one
    isGlobal: bool,     // Load/Store/AddrOf: the name is a file global, not a frame slot
    firstArg: long, argCount: long,     // Call arguments, as a run
    // Asm pieces, as a run. They have fields of their own rather than reusing the argument ones:
    // everything that walks uses (liveness, the allocator) reads `args` through `firstArg`, and
    // an asm block indexing a different table there would send them off the end of it.
    firstPiece: long, pieceCount: long,
    kind:     Lit,      // the result or operation type
    fromKind: Lit,      // Convert: the source type
    toKind:   Lit,      // Convert: the target type
    // PtrLoad/PtrStore: an index scaled by 1, 2, 4 or 8 and added to the address, so `p[i]` is one
    // addressing mode. Only `Scaler` (scale.k) sets it, after every other pass has run; before
    // it `x` is NO_TEMP everywhere.
    x:        Temp,
    scale:    long
}

pub instr op:IROp -> Instr {
    return Instr { op: op, dst: NO_TEMP, a: NO_TEMP, b: NO_TEMP, imm: 0,
                   bIsImm: false, bImm: 0, paramSeed: false, promoted: false, noReturn: false, cmpOp: IROp.CmpEq,
                   name: NO_SYM, structName: NO_SYM, isGlobal: false,
                   firstArg: 0, argCount: 0, firstPiece: 0, pieceCount: 0,
                   kind: Lit.Void, fromKind: Lit.Void, toKind: Lit.Void, x: NO_TEMP, scale: 0 };
}

// A `Convert` that hands on the same address under another of the types an address travels as:
// a pointer, a `str` or a slice view of the same pair (`buf[..n] as str`, `s as [u8]`). The emitter
// writes it as a move.
pub addressConvert in:Instr -> bool {
    return in.op == IROp.Convert && viewKind(in.fromKind) && viewKind(in.toKind);
}
local viewKind k:Lit -> bool { return k == Lit.Ptr || k == Lit.Str || k == Lit.Slice; }

// How many bytes a string literal's text stands for: each backslash escape is one byte. This is
// the `len` the emitter writes into the literal's pair (`asm.k` `emitBytes`, which counts the
// same way as it writes the bytes).
pub literalLength text:str -> long {
    n: long = 0;
    i: long = 0;
    while (i < text.len) {
        if (charAt(text, i) == 92 && i + 1 < text.len) { i = i + 1; }
        n = n + 1;
        i = i + 1;
    }
    return n;
}

// One function's lowered body.
pub struct IRFunc {
    name: Sym,
    firstInstr: long, instrCount: long,   // into the program's flat instruction list
    // Temps are numbered across the whole program, so a function owns the half-open range
    // [firstTemp, tempCount): the ones made while this body was being lowered. The back end must
    // work in that range and no wider. Sized from `tempCount` alone, every function's allocator,
    // liveness bitsets and spill area would cover every temp in the program: a two-line accessor
    // got a spill slot for each of a hundred thousand temps, 866KB of stack for a function that
    // used forty bytes, and the compiler ran out of stack compiling itself.
    firstTemp: Temp, tempCount: long,
    // One temp reserved per named scalar slot this body loads or stores, so `Opt.promoteLocals`
    // can put a local in a register. The lowerer reserves them while the function's temp range is
    // still open. A temp made afterwards would be numbered past `tempCount`, and the allocator,
    // which works in `[firstTemp, tempCount)` and nowhere else, would take it for another
    // function's and spill it. A reservation that promotion then declines costs nothing: a temp
    // nothing reads gets no live range and no register.
    firstPromo: long, promoCount: long,     // into the program's `promoName`/`promoTemp`
    // `pub`, so another object may call it: the emitter gives it a `global` directive. `pkg` and
    // `local` are internal to this object and need none. They differ from each other only in
    // what the checker allows, never in what the linker sees.
    isPub: bool,
    isMain: bool,
    // `main args: ...str`: the entry stub has to marshal the OS argv into a slice before it
    // calls. Recorded here because only the lowerer can see the declaration.
    wantsArgs: bool,
    // Another package's function, read from its `.klib` only to be copied into callers here
    // (`irpack.importInlinable`): never emitted, and gone once the inliner has run.
    imported: bool,
    // It holds a `recover` statement (`hasRecover`), as the lowerer found.
    holdsRecover: bool,
    // Its parameters' conventions, by position in the IR (a hidden `$sret` first), as the checker
    // settled them: bit k of `borrows` says parameter k is a borrow (`read` or `inout`: a struct,
    // a `&self`, an `inout` scalar). A borrow's own bytes are written during the call only through
    // it: the law of exclusivity keeps a borrow written (an `inout` one, or a `&T` the function
    // writes through) apart from every other argument, and a `var` global lent apart from what the
    // call writes by name. That is what `flow.k` trusts of them. A function declared `unsafe` may
    // keep or alias what it is lent, so it says nothing (`isUnsafe`).
    borrows: long,
    isUnsafe: bool
}

// The whole program, lowered. Instructions and call arguments are flat, and each function names a
// run: the same shape the syntax tree uses, for the same reason.
pub struct IRProgram {
    code:  Vec<Instr>,
    args:  Vec<Temp>,
    funcs: Vec<IRFunc>,

    tempKinds:  Vec<Lit>,     // every temp's type, indexed by temp id
    tempStructs: Vec<Sym>,    // and its companion name, when the type needs one

    // Every temp holding a `*T` must record its pointee here. This map, not the static type, is
    // what makes `p + n` scale by `sizeof(T)`, `q - p` an element count, and `*p` a load of the
    // pointee's width. An untracked pointer silently degrades to `*long`: byte arithmetic and
    // eight-byte loads.
    tempPointees: Vec<Sym>,

    // Inline assembly, flattened: an `Asm` instruction names a run here through its argument
    // fields, which it has no other use for.
    asmKinds: Vec<AsmKind>,
    asmRegs:  Vec<Sym>,
    asmNames: Vec<Sym>,
    asmVals:  Vec<Temp>,
    asmText:  Vec<Sym>,
    // How wide the value bound to each `in`/`out` register is. A `{reg}` placeholder in the
    // programmer's assembly renders as the sub-register of that width, which is what lets one
    // generic body serve every operand size (`al`/`ax`/`eax`/`rax`).
    asmSizes: Vec<long>,

    globals: Vec<Sym>,        // file globals, each one label in `.data`
    globalIx: HashMap<long, long>,   // a global's name (its number) -> its index in `globals`
    globalBytes: Vec<long>,
    // A scalar global whose initializer folded to a constant carries it here and is emitted
    // with it, so nothing runs at startup for it. `globalHasInit` says which ones.
    globalInits: Vec<long>,
    globalHasInit: Vec<bool>,
    // The images the evaluator computed (`Ast.images`, carried whole so a block's index is the
    // same here): a global's bytes, or a heap block's, with the pointer words in them named.
    // `globalImage` is the image index of each global that has one, -1 otherwise.
    globalImage: Vec<long>,
    imageFirst: Vec<long>,
    imageCount: Vec<long>,
    imageRelocFirst: Vec<long>,
    imageRelocCount: Vec<long>,
    imageIsBlock: Vec<bool>,
    imageBytes: Vec<u8>,
    relocOffset: Vec<long>,
    relocKind: Vec<RelocKind>,
    relocTarget: Vec<long>,     // Str: the string's index; Global/Vtable/Fn: the name, as a Sym; Block: the image
    relocDelta: Vec<long>,

    // The reserved promotion temps, as a flat run per function. Parallel: `promoName[i]` is the
    // variable and `promoTemp[i]` the temp standing in for it. (Not to be confused with
    // `slotAt`/`slotBytes` below, which are how wide each named slot is.)
    promoName: Vec<Sym>,
    promoTemp: Vec<Temp>,

    // Functions this object calls and does not define: a `pub` declaration with no body. The
    // emitter writes an `extern` directive for each one it actually reaches, and the linker finds
    // the body in another object.
    externs: Vec<Sym>,

    strings: Vec<Sym>,        // string literals, in the order they were first seen
    stringIx: HashMap<long, long>,   // a literal's text (its number) -> its index in `strings`
    aggSlots: Vec<long>,      // the size of each hidden aggregate scratch slot

    // How many bytes each named variable's storage needs. A scalar is one register, but an array
    // or a struct is its whole block, and only the declaration knows that, which is why it is
    // recorded here rather than derived from the instructions that touch it. By name across the
    // program (the widest declaration of a name wins), found through `slotAt`: the name's number
    // -> its entry. Asked once per declaration and once per slot of every function, so a lookup,
    // not a walk over every name the program has.
    slotAt: HashMap<long, long>,
    slotBytes: Vec<long>,
    // The same per function, keyed by (the function's name << 32 | the slot's name): the widest
    // of its own declarations of the slot, and of a spliced body's (`fnSlotBytesOf`). Frames are
    // laid out from these. Sized by the name across the program, `Vec<Expr>.get`'s frame was 368
    // bytes for a slot that held eight, because some other function's `e` was an `Expr`.
    // `slotFn` is the function the lowerer is in, which `noteSlot` records for.
    fnSlotAt: HashMap<long, long>,
    slotFn: Sym,
    // While the lowerer is inside a `recover` body: its handler's label. Each call and `asm` block
    // emitted meanwhile is followed by a `FaultEdge` to it.
    faultTo: Sym
}

methods IRProgram for Default {
    new -> IRProgram {
        return IRProgram { code: vec![], args: vec![], funcs: vec![], tempKinds: vec![], tempStructs: vec![],
                           tempPointees: vec![],
                           asmKinds: vec![], asmRegs: vec![], asmNames: vec![], asmVals: vec![], asmText: vec![], asmSizes: vec![],
                           globals: vec![], globalIx: map![], globalBytes: vec![], globalInits: vec![], globalHasInit: vec![],
                           globalImage: vec![], imageFirst: vec![], imageCount: vec![],
                           imageRelocFirst: vec![], imageRelocCount: vec![], imageIsBlock: vec![], imageBytes: vec![],
                           relocOffset: vec![], relocKind: vec![], relocTarget: vec![], relocDelta: vec![],
                           strings: vec![], stringIx: map![],
                           aggSlots: vec![], slotAt: map![], slotBytes: vec![], fnSlotAt: map![], slotFn: NO_SYM, faultTo: NO_SYM,
                           promoName: vec![], promoTemp: vec![], externs: vec![] };
    }
}

methods IRProgram {
    // One temp per named scalar slot in the instructions `[from, code.len())`: the body just
    // lowered. Called before the `IRFunc` is pushed, so every temp made here lands inside the
    // range that function is about to claim. A global is not a slot, and an aggregate's slot is
    // the value rather than a holder of one.
    reservePromotions &self from:long -> long {
        first: long = self.promoName.len();
        for i in from..self.code.len() {
            in: Instr = self.code.get(i);
            if (in.op != IROp.Load && in.op != IROp.Store) { continue; }
            if (in.isGlobal || in.name == NO_SYM) { continue; }
            // A backed enum or a distinct type is an integer in its slot, like any scalar.
            if ((isAggregate(in.kind) && !namedScalar(in.kind, in.structName)) || in.kind == Lit.Void) { continue; }
            seen: bool = false;
            k: long = first;
            while (k < self.promoName.len()) {
                if (self.promoName.get(k) == in.name) { seen = true; k = self.promoName.len(); }
                else { k = k + 1; }
            }
            if (seen) { continue; }
            self.promoName.push(in.name);
            self.promoTemp.push(self.newTemp(in.kind, in.structName));
        }
        return first;
    }

    // A fresh temp of the given type.
    // A `*T` carries its pointee in `tempPointees`, not in its static type: that table is what
    // makes `p + n` scale by sizeof(T), `q - p` an element count, and `*p` a load of the right
    // width. A pointer temp made without it silently degrades to `*long`, so the companion name a
    // `*T` already holds is recorded here, the one place every temp is made.
    newTemp &self k:Lit sname:Sym -> Temp {
        self.tempKinds.push(k);
        self.tempStructs.push(sname);
        pointee: Sym = NO_SYM;
        if (k == Lit.Ptr) { pointee = sname; }
        self.tempPointees.push(pointee);
        return self.tempKinds.len() - 1;
    }

    kindOf &self t:Temp -> Lit {
        if (t < 0 || t >= self.tempKinds.len()) { return Lit.Void; }
        return self.tempKinds.get(t);
    }
    structOf &self t:Temp -> Sym {
        if (t < 0 || t >= self.tempStructs.len()) { return NO_SYM; }
        return self.tempStructs.get(t);
    }

    // Record what `t` points at. The one funnel for that fact: call it at every producer of a
    // pointer value (a local load, a field read, a global read, a call result, a cast to `*T`),
    // and conversely erase it on a cast away from `*T`, or `(a as long) - (b as long)` silently
    // stays scaled.
    notePointee &self t:Temp pointee:Sym -> void {
        if (t < 0 || t >= self.tempPointees.len()) { return; }
        self.tempPointees.set(t, pointee);
    }
    pointeeOf &self t:Temp -> Sym {
        if (t < 0 || t >= self.tempPointees.len()) { return NO_SYM; }
        return self.tempPointees.get(t);
    }

    // One piece of an inline assembly block, in source order.
    addAsmPiece &self k:AsmKind reg:Sym name:Sym v:Temp text:Sym size:long -> long {
        self.asmSizes.push(size);
        self.asmKinds.push(k);
        self.asmRegs.push(reg);
        self.asmNames.push(name);
        self.asmVals.push(v);
        self.asmText.push(text);
        return self.asmKinds.len() - 1;
    }

    // Record a file global and how much storage it needs. Deduplicated, because every module that
    // reads one mentions it.
    noteGlobal &self name:Sym bytes:long -> void {
        if (self.globalIx.has(name as long)) { return; }
        self.globalIx.put(name as long, self.globals.len());
        self.globals.push(name);
        self.globalBytes.push(bytes);
        self.globalInits.push(0);
        self.globalHasInit.push(false);
        self.globalImage.push(-1);
    }
    setGlobalInit &self name:Sym value:long -> void {
        hit: Option<long> = self.globalIx.find(name as long);
        match hit { Some(i) { self.globalInits.set(i, value); self.globalHasInit.set(i, true); } None { } }
    }
    // Which global carries which image. The images themselves arrive through `addImage`.
    setGlobalImage &self name:Sym image:long -> void {
        hit: Option<long> = self.globalIx.find(name as long);
        match hit { Some(i) { self.globalImage.set(i, image); } None { } }
    }
    // One image, appended in the same order as `Ast.images` so indexes agree; the bytes and
    // relocations follow through `imageByte` and `imageReloc`.
    addImage &self isBlock:bool -> void {
        self.imageFirst.push(self.imageBytes.len());
        self.imageCount.push(0);
        self.imageRelocFirst.push(self.relocOffset.len());
        self.imageRelocCount.push(0);
        self.imageIsBlock.push(isBlock);
    }
    imageByte &self b:u8 -> void {
        self.imageBytes.push(b);
        last: long = self.imageCount.len() - 1;
        self.imageCount.set(last, self.imageCount.get(last) + 1);
    }
    imageReloc &self offset:long kind:RelocKind target:long delta:long -> void {
        self.relocOffset.push(offset);
        self.relocKind.push(kind);
        self.relocTarget.push(target);
        self.relocDelta.push(delta);
        last: long = self.imageRelocCount.len() - 1;
        self.imageRelocCount.set(last, self.imageRelocCount.get(last) + 1);
    }
    // Asked of every variable the lowerer reads or writes: a lookup, not a walk over every global.
    isGlobalName &self name:Sym -> bool { return self.globalIx.has(name as long); }

    // Record how much storage a named variable needs.
    noteSlot &self name:Sym bytes:long -> void {
        self.noteFnSlot(self.slotFn, name, bytes);
        hit: Option<long> = self.slotAt.find(name as long);
        match hit {
            Some(i) { if (bytes > self.slotBytes.get(i)) { self.slotBytes.set(i, bytes); } }
            None {
                self.slotAt.put(name as long, self.slotBytes.len());
                self.slotBytes.push(bytes);
            }
        }
    }
    // Record it for function `fn` too.
    noteFnSlot &self fn:Sym name:Sym bytes:long -> void {
        if (fn == NO_SYM || name == NO_SYM) { return; }
        key: long = ((fn as long) << 32) | (name as long);
        hit: Option<long> = self.fnSlotAt.find(key);
        match hit {
            Some(b) { if (bytes > b) { self.fnSlotAt.put(key, bytes); } }
            None { self.fnSlotAt.put(key, bytes); }
        }
    }
    // How wide a slot of function `fn` is: from its own declarations, or the name's widest.
    fnSlotBytesOf &self fn:Sym name:Sym -> long {
        if (fn != NO_SYM && name != NO_SYM) {
            hit: Option<long> = self.fnSlotAt.find(((fn as long) << 32) | (name as long));
            match hit { Some(b) { return b; } None { } }
        }
        return self.slotBytesOf(name);
    }
    slotBytesOf &self name:Sym -> long {
        hit: Option<long> = self.slotAt.find(name as long);
        match hit { Some(i) { return self.slotBytes.get(i); } None { } }
        return 8;
    }

    // Kept this small so that it is copied into its callers: it is called for every instruction.
    emit &self in:Instr -> long {
        self.code.push(in);
        if (self.faultTo != NO_SYM) { return self.faultAfter(); }
        return self.code.len() - 1;
    }
    // Inside a `recover` body, a call or an `asm` block just emitted may raise: a `FaultEdge` to
    // the handler follows it, and a call that never returns is not marked so, since it may still
    // leave for the handler. The index of the instruction emitted.
    faultAfter &self -> long {
        at: long = self.code.len() - 1;
        if (!clobbersRegisters(self.code[at].op)) { return at; }
        c: Instr = self.code.get(at);
        c.noReturn = false;
        self.code.set(at, c);
        fe: Instr = instr(IROp.FaultEdge);
        fe.name = self.faultTo;
        self.code.push(fe);
        return at;
    }

    // The hidden pointer a struct-returning function writes its result through. It is the
    // function's first argument, before any it was written with, which is why every other
    // argument shifts by one when the return type is an aggregate.
    sretName -> Sym { return intern("$sret"); }

    // The index a string literal was given, adding it if this is the first sighting. Literals are
    // deduplicated so identical text shares one label in `.data`.
    internString &self s:Sym -> long {
        hit: Option<long> = self.stringIx.find(s as long);
        match hit { Some(i) { return i; } None { } }
        self.stringIx.put(s as long, self.strings.len());
        self.strings.push(s);
        return self.strings.len() - 1;
    }

    // A hidden scratch slot for an aggregate result. `AggSlot.imm` is a position in this list, not
    // a size: splicing a function body elsewhere must offset those indices by where its slots
    // were appended, or the wrong memory is read, silently.
    addAggSlot &self size:long -> long {
        self.aggSlots.push(size);
        return self.aggSlots.len() - 1;
    }
}

// Up to `UNROLL_BYTES`, a block zero is one store per word. Up to `UNROLL_COPY_BYTES`, a block
// copy is one move per word, and so is a struct literal's zero fill, which `lower.zeroFill`
// writes a word at a time. Past them each is a single `rep stosq` or `rep movsq`, whose fixed
// start-up cost the unrolled moves stay under. The copy limit is the larger because the
// compiler's own `Instr` is 136 bytes and is copied everywhere: with the limit at 128, doing
// those copies as `rep movsq` cost the compiler 14% of its time.
pub UNROLL_BYTES: long = 128;
pub UNROLL_COPY_BYTES: long = 512;

// Whether `fn` holds a `recover` statement. Such a function's handler can be entered from the
// middle of its body, which the passes that keep a value in a register or move code between
// blocks are not built to follow, so they leave it alone.
pub hasRecover p:IRProgram fn:IRFunc -> bool { return fn.holdsRecover; }
