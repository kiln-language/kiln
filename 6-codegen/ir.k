// Typed three-address IR.
//
// Every operand is a virtual register (a "temp") and a constant is materialised into one by
// `Const`, so operands are uniform. Each temp carries a type, so the back end derives operand
// widths and extensions from types rather than assuming eight bytes everywhere.
#include <parse::{ast, registry, types}>
#include <support::compiler>
#include <stdlib::{map, option, string, vec}>

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
    PtrLoad,    // dst = [a + imm]
    PtrStore,   // [a + imm] = b
    AggCopy,    // memcpy [a] <- [b], imm bytes
    AggZero,    // memset [a] <- 0, imm bytes: a local array declared without a value
    Bounds,     // trap unless (unsigned) a < b
    StrLitVal,  // dst = the address of a 16-byte {ptr, len} constant
    AggSlot,    // dst = the address of hidden aggregate scratch slot #imm
    VtableAddr, // dst = the address of the vtable named <name>
    FnAddr,     // dst = the address of the function named <name>
    CallIndirect,  // dst = (*a)(args...): through a pointer, which is what a vtable slot holds

    // A fused compare-and-branch. It was the optimizer that made these, which is why the IR
    // has the shape it has; the lowerer makes them too now, ever since a condition became
    // control flow and `branchUnless` started ending a block with the comparison itself.
    // Anything reading the IR straight out of lowering meets one.
    Jcc,        // if (a <cmpOp> b) jump: a fused compare-and-branch

    // A deleted instruction. The instruction list is flat across the program and every `IRFunc`
    // names a run in it by index, so removing an entry would move every function after it. A
    // pass blanks one instead, and everything that walks the list skips it: the emitter, the
    // CFG, the allocator. Nothing else ever produces one.
    Nop
}

// The two "what does this wreck?" questions, asked by the register allocator and by the caching
// passes. They live beside the opcode list because that is the one place a new opcode is certain
// to be looked at; kept anywhere else, an op missing from one of them is a silently wrong
// allocation or a stale cached load: never a crash.
pub clobbersRegisters op:IROp -> bool {
    return op == IROp.Call || op == IROp.CallIndirect || op == IROp.Asm;
}
// May write memory that cannot be named. Anything reachable through a pointer. `ArrStore` is
// deliberately absent: it writes one element of a local array, and array slots are disjoint from
// the named scalar slots the load cache keys on.
pub clobbersMemory op:IROp -> bool {
    return clobbersRegisters(op) || op == IROp.PtrStore || op == IROp.AggCopy || op == IROp.AggZero;
}

// An aggregate a callee owns a copy of, rather than a borrow of the caller's. A struct and a
// tuple are values, so the prologue copies them into storage of their own; `str`, a slice and a
// trait object are already pointers to their own pair, and a `Ref` is a borrow by definition.
pub byValueAggregate k:Lit -> bool { return k == Lit.Struct || k == Lit.Tuple; }

pub isCompare op:IROp -> bool {
    return op == IROp.CmpEq || op == IROp.CmpNe || op == IROp.CmpLt
        || op == IROp.CmpGt || op == IROp.CmpLe || op == IROp.CmpGe;
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
    return isBranch(op) || op == IROp.Ret || op == IROp.RetVoid;
}

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

    // A `paramSeed` load whose variable `Opt::promoteLocals` promoted. The prologue drains every
    // argument register to its slot before anything else: a promoted parameter's temp could
    // otherwise be given a register a later argument is still sitting in, so the seed stays and
    // is emitted, once, as the load that fills the temp from the slot the prologue just wrote.
    // Without it the seed is skipped, as it always was: the body reads the slot by name.
    promoted: bool,

    // A `Call` to a function that never returns (`panicIndex`, `sysExit`, anything the checker
    // found always ends in one): no path leaves it, so a block ends there with no successor. It
    // is what lets a bounds check's facts survive past its panic.
    noReturn: bool,

    // A `@name(...)` call. Its target is a hand-written symbol in `print.s`, linked beside the
    // program: the name is the symbol and is neither mangled nor declared anywhere in Kiln,
    // so the emitter has to be told rather than deduce it from the name.

    cmpOp: IROp,        // Jcc only: which comparison to branch on
    name:  Sym,         // variable, function, or label
    structName: Sym,    // the aggregate `kind` names, when it names one
    isGlobal: bool,     // Load/Store/AddrOf: the name is a file global, not a frame slot
    firstArg: long, argCount: long,     // Call arguments, as a run
    // Asm pieces, as a run. Their own fields rather than the argument ones: everything that walks
    // uses (liveness, the allocator) reads `args` through firstArg, and an asm block indexing a
    // different table there sends them off the end of it.
    firstPiece: long, pieceCount: long,
    kind:     Lit,      // the result or operation type
    fromKind: Lit,      // Convert: the source type
    toKind:   Lit       // Convert: the target type
}

pub instr op:IROp -> Instr {
    return Instr { op: op, dst: NO_TEMP, a: NO_TEMP, b: NO_TEMP, imm: 0,
                   bIsImm: false, bImm: 0, paramSeed: false, promoted: false, noReturn: false, cmpOp: IROp.CmpEq,
                   name: NO_SYM, structName: NO_SYM, isGlobal: false,
                   firstArg: 0, argCount: 0, firstPiece: 0, pieceCount: 0,
                   kind: Lit.Void, fromKind: Lit.Void, toKind: Lit.Void };
}

// One function's lowered body.
pub struct IRFunc {
    name: Sym,
    firstInstr: long, instrCount: long,   // into the program's flat instruction list
    // Temps are numbered across the whole program, so a function owns the half-open range
    // [firstTemp, tempCount): the ones lowering made while this body was being lowered. The back
    // end must work in that range and no wider. Sized from `tempCount` alone, every function's
    // allocator, liveness bitsets and spill area covered every temp in the program: a two-line
    // accessor got a frame with a spill slot for all hundred thousand of them, 866KB of stack for
    // a function that used forty bytes, and the compiler ran out of stack compiling itself.
    firstTemp: Temp, tempCount: long,
    // One temp reserved per named scalar slot this body loads or stores, so `Opt::promoteLocals`
    // can put a local in a register. Reserved by the lowerer, while the function's temp range is
    // still open: a temp made afterwards would be numbered past `tempCount` and the allocator,
    // which works in `[firstTemp, tempCount)` and nowhere else, would call it another function's
    // and spill it. Reserving one that promotion then declines costs nothing: a temp nothing
    // reads gets no live range and no register.
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
    imported: bool
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
    aggSlots: Vec<long>,      // the size of each hidden aggregate scratch slot

    // How many bytes each named variable's storage needs. A scalar is one register, but an array
    // or a struct is its whole block, and only the declaration knows that, which is why it is
    // recorded here rather than derived from the instructions that touch it. By name across the
    // program (the widest declaration of a name wins), found through `slotAt`: the name's number
    // -> its entry. Asked once per declaration and once per slot of every function, so a lookup,
    // not a walk over every name the program has.
    slotAt: HashMap<long, long>,
    slotBytes: Vec<long>
}

methods IRProgram for Default {
    new -> IRProgram {
        return IRProgram { code: vec![], args: vec![], funcs: vec![], tempKinds: vec![], tempStructs: vec![],
                           tempPointees: vec![],
                           asmKinds: vec![], asmRegs: vec![], asmNames: vec![], asmVals: vec![], asmText: vec![], asmSizes: vec![],
                           globals: vec![], globalBytes: vec![], globalInits: vec![], globalHasInit: vec![],
                           globalImage: vec![], imageFirst: vec![], imageCount: vec![],
                           imageRelocFirst: vec![], imageRelocCount: vec![], imageIsBlock: vec![], imageBytes: vec![],
                           relocOffset: vec![], relocKind: vec![], relocTarget: vec![], relocDelta: vec![],
                           strings: vec![],
                           aggSlots: vec![], slotAt: map![], slotBytes: vec![],
                           promoName: vec![], promoTemp: vec![], externs: vec![] };
    }
}

methods IRProgram {
    // A fresh temp of the given type.
    // A `*T` carries its pointee here, not in its static type: that map is what makes `p + n`
    // scale by sizeof(T), `q - p` an element count, and `*p` a load of the right width. A pointer
    // temp created without it silently degrades to `*long`, so the companion name a `*T` already
    // holds is recorded at the one place every temp is made.
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
        for i in 0..self.globals.len() {
            if (self.globals.get(i) == name) { return; }
        }
        self.globals.push(name);
        self.globalBytes.push(bytes);
        self.globalInits.push(0);
        self.globalHasInit.push(false);
        self.globalImage.push(-1);
    }
    setGlobalInit &self name:Sym value:long -> void {
        for i in 0..self.globals.len() {
            if (self.globals.get(i) == name) {
                self.globalInits.set(i, value);
                self.globalHasInit.set(i, true);
                return;
            }
        }
    }
    // Which global carries which image. The images themselves arrive through `addImage`.
    setGlobalImage &self name:Sym image:long -> void {
        for i in 0..self.globals.len() {
            if (self.globals.get(i) == name) { self.globalImage.set(i, image); return; }
        }
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
    isGlobalName &self name:Sym -> bool {
        for i in 0..self.globals.len() {
            if (self.globals.get(i) == name) { return true; }
        }
        return false;
    }

    // Record how much storage a named variable needs.
    noteSlot &self name:Sym bytes:long -> void {
        hit: Option<long> = self.slotAt.find(name as long);
        match hit {
            Some(i) { if (bytes > self.slotBytes.get(i)) { self.slotBytes.set(i, bytes); } }
            None {
                self.slotAt.put(name as long, self.slotBytes.len());
                self.slotBytes.push(bytes);
            }
        }
    }
    slotBytesOf &self name:Sym -> long {
        hit: Option<long> = self.slotAt.find(name as long);
        match hit { Some(i) { return self.slotBytes.get(i); } None { } }
        return 8;
    }

    emit &self in:Instr -> long {
        self.code.push(in);
        return self.code.len() - 1;
    }

    // The hidden pointer a struct-returning function writes its result through. It is the
    // function's first argument, before any it was written with, which is why every other
    // argument shifts by one when the return type is an aggregate.
    sretName -> Sym { return intern("$sret"); }

    // The index a string literal was given, adding it if this is the first sighting. Literals are
    // deduplicated so identical text shares one label in `.data`.
    internString &self s:Sym -> long {
        for i in 0..self.strings.len() {
            if (self.strings.get(i) == s) { return i; }
        }
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

// Up to this many bytes a block zero is one store per word, and a block copy (or a struct
// literal's zero fill, which `lower.zeroFill` otherwise writes a word at a time) one move per word;
// past them one `rep stosq` or `rep movsq`, whose fixed start-up cost the unrolled moves stay under.
// A copy's is the larger: the compiler's own `Instr` is 136 bytes, copied everywhere, and at 128
// its copies as `rep movsq` cost the compiler 14% of its time.
pub UNROLL_BYTES: long = 128;
pub UNROLL_COPY_BYTES: long = 512;
