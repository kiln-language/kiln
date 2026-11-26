// The IR as textual LLVM IR, for `--emit=llvm`.
//
// This is a second consumer of `IRProgram`, beside `asm.k`. The native back end stays the one the
// seed is built with, so `bootstrap/kilnc` can still be remade with nothing but NASM and ld; this
// one hands a program to LLVM for when its optimizer is worth more than the seconds it costs.
//
// Two properties of the IR keep the translation short, and both exist for other reasons. Every
// scalar temp already holds a canonical 64-bit word, so everything is `i64` and nothing narrower.
// And the IR is not SSA but loads and stores against named slots, so each temp and each slot
// becomes an `alloca` and LLVM's `mem2reg` builds the SSA. Nothing here places a phi, which is
// usually the expensive half of writing a back end like this one.
//
// Pointers are written `ptr`, not `i64*`: LLVM 15 made pointers opaque and 17 removed the typed
// form, so the older spelling is rejected outright by anything current.
//
// The optimizer and the inliner are skipped on this path, since LLVM does that work, so promoted
// temps never reach here. A `Jcc` still can, because the lowerer makes those too.
#include <ir>
#include <lower>        // the `@init`/`@fini` hooks `_start` calls
#include <asm>          // regNameSized / regIndexOf: the register naming is asm.k's
#include <parse::{ast, types, registry}>
#include <support::compiler>
#include <stdlib::{fmt, map, option, string, vec}>

// What is not translated yet. It is refused by name rather than emitted wrongly: a back end that
// quietly produces the wrong instruction is the one kind of bug this compiler has spent the most
// time on.
local unsupported what:str -> void {
    failStr(format("`--emit=llvm` cannot translate {} yet\nhelp: build without `--emit=llvm` to use the native back end, which handles it", what));
}

// The LLVM predicate a comparison opcode means, over an unsigned type or a signed one. The
// native back end picks `ja` or `jg` by the same test (`typeInfo(kind).unsignedNum`), and a `u64`
// past 2^63 compared as signed reads as negative.
local llvmPred op:IROp uns:bool -> str {
    if (op == IROp.CmpEq) { return "eq"; }
    if (op == IROp.CmpNe) { return "ne"; }
    if (uns) {
        if (op == IROp.CmpLt) { return "ult"; }
        if (op == IROp.CmpGt) { return "ugt"; }
        if (op == IROp.CmpLe) { return "ule"; }
        if (op == IROp.CmpGe) { return "uge"; }
    }
    if (op == IROp.CmpLt) { return "slt"; }
    if (op == IROp.CmpGt) { return "sgt"; }
    if (op == IROp.CmpLe) { return "sle"; }
    if (op == IROp.CmpGe) { return "sge"; }
    unsupported("this comparison");
    return "eq";
}

// The ordered predicate for a float comparison (false on a NaN), `une` for `!=` (true on one).
local llvmFloatPred op:IROp -> str {
    if (op == IROp.CmpEq) { return "oeq"; }
    if (op == IROp.CmpNe) { return "une"; }
    if (op == IROp.CmpLt) { return "olt"; }
    if (op == IROp.CmpGt) { return "ogt"; }
    if (op == IROp.CmpLe) { return "ole"; }
    return "oge";
}

// The bytes a value of this kind occupies in memory, the way `asm.k` sizes a load: a slot is
// always a word, but what a pointer names is the real thing.
local widthOfKind k:Lit -> long {
    w: long = typeInfo(k).size;
    if (w < 1 || w > 8) { return 8; }
    if (w == 3) { return 4; }
    if (w > 4) { return 8; }
    return w;
}
local intBits w:long -> String {
    s: String;
    s.pushStr("i");
    s.pushLong(w * 8);
    return s;
}

// An LLVM IR string constant takes `\XX` hex escapes and nothing else: a newline is `\0A`, a
// quote `\22`, a backslash `\5C`.
local escapeAsm s:str -> String {
    out: String;
    for i in 0..s.len {
        c: long = charAt(s, i);
        if (c == 10)      { out.pushStr("\\0A"); }
        else if (c == 34) { out.pushStr("\\22"); }
        else if (c == 92) { out.pushStr("\\5C"); }
        else              { out.push(c as char); }
    }
    return out;
}

// The caller-saved registers, which an `asm` block clobbers unless it bound them: this IR says a
// block clobbers like a call. `sysExit` is the case that needs it: it writes `rax` in its text and
// declares no `out`, so without a clobber LLVM may believe a live value survived there.
local callerSavedName i:long -> str {
    if (i == 0) { return "rax"; }
    if (i == 1) { return "rcx"; }
    if (i == 2) { return "rdx"; }
    if (i == 3) { return "rsi"; }
    if (i == 4) { return "rdi"; }
    if (i == 5) { return "r8"; }
    if (i == 6) { return "r9"; }
    if (i == 7) { return "r10"; }
    return "r11";
}

// A byte, as an LLVM `c"..."` element: printable ASCII stands for itself, everything else is a
// two-digit hex escape. `"` and the escape character itself have to be escaped too.
local hexDigit v:long -> char {
    if (v < 10) { return ('0' + v) as char; }
    return ('a' + (v - 10)) as char;
}
local pushByte inout out:String b:long -> void {
    if (b >= 32 && b < 127 && b != 34 && b != 92) { out.push(b as char); return; }
    out.push('\\');
    out.push(hexDigit((b / 16) & 15));
    out.push(hexDigit(b & 15));
}

// The symbol a relocation points at, spelled the way this back end names that kind of thing.
local relocSymbol p:IRProgram k:RelocKind target:long -> String {
    s: String;
    // Each case supplies its own sigil: a block is not a symbol but a constant expression naming
    // an offset inside its region, and `@` in front of `getelementptr` is not a name.
    if (k == RelocKind.Str)    { s.pushStr("@strb."); s.pushLong(target); return s; }
    if (k == RelocKind.Block)  {
        s.pushStr("getelementptr (i8, ptr @ctbr.");
        s.pushLong(target);
        s.pushStr(", i64 16)");
        return s;
    }
    if (k == RelocKind.Global) { s.pushStr("@\""); s.pushStr(globalSymbol(nameOf(target))); s.pushStr("\""); return s; }
    s.pushStr("@\"");
    s.pushStr(nameOf(target));
    s.pushStr("\"");
    return s;
}

pub struct LlvmEmitter {
    out: String,
    nextVal: long,      // %v0, %v1, ...: one SSA name per value produced
    nextLbl: long,      // the fallthrough labels a conditional branch needs
    // Set once the current block has a terminator, so a fallthrough into the next label gets the
    // explicit `br` LLVM requires and nothing is emitted after a `ret`.
    closed: bool,
    slots: HashMap<str, bool>,
    // The `file:line` texts a failed bounds check reports, each emitted once as `@bndloc.N`.
    locs: Vec<Sym>,
    locAt: HashMap<long, long>,
    needBounds: bool,
    // The function being written, for what an `asm` block's output needs to know of its slot.
    fnFirst: long, fnCount: long
}

methods LlvmEmitter for Default {
    new -> LlvmEmitter {
        s: String;
        m: HashMap<str, bool>;
        return LlvmEmitter { out: s, nextVal: 0, nextLbl: 0, closed: false, slots: m,
                             locs: vec![], locAt: map![], needBounds: false, fnFirst: 0, fnCount: 0 };
    }
}

// LLVM allows `::` and `$` only inside a quoted name, so every Kiln symbol is quoted and nothing
// has to be mangled or made unique.
local quoted n:str -> String {
    s: String;
    s.push('"');
    s.pushStr(n);
    s.push('"');
    return s;
}

methods LlvmEmitter {
    line &self s:str -> void { self.out.pushStr(s); self.out.push('\n'); }
    put  &self s:str -> void { self.out.pushStr(s); }
    putString &self s:String -> void { unsafe { self.out.pushStr(s.view()); } }
    putNum &self v:long -> void { self.out.pushLong(v); }
    // A word cut to its low `w` bytes, as the `i8`..`i32` an access of that width takes.
    narrowTo &self v:String w:long -> String {
        if (w >= 8) { return v; }
        n: String = self.fresh();
        self.put("  ");
        self.putString(n);
        self.put(" = trunc i64 ");
        self.putString(v);
        self.put(" to ");
        self.putString(intBits(w));
        self.line("");
        return n;
    }

    fresh &self -> String {
        v: String;
        v.pushStr("%v");
        v.pushLong(self.nextVal);
        self.nextVal = self.nextVal + 1;
        return v;
    }
    freshLabel &self -> String {
        v: String;
        v.pushStr("ll.");
        v.pushLong(self.nextLbl);
        self.nextLbl = self.nextLbl + 1;
        return v;
    }

    tempSlot &self t:Temp -> String {
        s: String;
        s.pushStr("%t");
        s.pushLong(t);
        return s;
    }
    // A named variable's slot. The name is quoted, so two locals cannot collide however they are
    // spelled, and a Kiln name never has to be rewritten to be a legal LLVM one.
    nameSlot &self n:Sym -> String {
        s: String;
        s.pushStr("%\"s.");
        s.pushStr(nameOf(n));
        s.push('"');
        return s;
    }
    // A label, quoted the same way: a Kiln label is spelled `.L6`, which is not a bare LLVM
    // identifier. The sigil belongs outside the quotes and everything else inside.
    labelRef &self n:Sym -> String {
        s: String;
        s.pushStr("%\"");
        s.pushStr(nameOf(n));
        s.push('"');
        return s;
    }
    labelDef &self n:Sym -> String {
        s: String;
        s.push('"');
        s.pushStr(nameOf(n));
        s.pushStr("\":");
        return s;
    }
    appendTo &self inout dst:String src:String -> void { unsafe { dst.pushStr(src.view()); } }

    locIndex &self s:Sym -> long {
        hit: Option<long> = self.locAt.find(s as long);
        match hit { Some(i) { return i; } None { } }
        self.locAt.put(s as long, self.locs.len());
        self.locs.push(s);
        return self.locs.len() - 1;
    }

    // Read a temp into a fresh value.
    readTemp &self t:Temp -> String {
        // `NO_TEMP` is the absence of an operand, not temp number -1. It can arrive here from an
        // instruction whose `b` is unused, and `%t-1` is not a name LLVM will take.
        if (t == NO_TEMP) {
            z: String;
            z.pushStr("0");
            return z;
        }
        v: String = self.fresh();
        self.put("  ");
        self.putString(v);
        self.put(" = load i64, ptr ");
        self.putString(self.tempSlot(t));
        self.line("");
        return v;
    }

    // An operand: a temp read, or the immediate the instruction encodes.
    operand &self in:Instr which:long -> String {
        if (which == 1 && in.bIsImm) {
            s: String;
            s.pushLong(in.bImm);
            return s;
        }
        t: Temp = in.a;
        if (which == 1) { t = in.b; }
        return self.readTemp(t);
    }

    writeTemp &self t:Temp v:String -> void {
        if (t == NO_TEMP) { return; }
        self.put("  store i64 ");
        self.putString(v);
        self.put(", ptr ");
        self.putString(self.tempSlot(t));
        self.line("");
    }

    binary &self in:Instr mnemonic:str -> void {
        x: String = self.operand(in, 0);
        y: String = self.operand(in, 1);
        r: String = self.fresh();
        self.put("  ");
        self.putString(r);
        self.put(" = ");
        self.put(mnemonic);
        self.put(" i64 ");
        self.putString(x);
        self.put(", ");
        self.putString(y);
        self.line("");
        self.writeTemp(in.dst, self.canonical(r, in.kind));
    }

    // `x` as the canonical word of type `k`: an operation narrower than a word wraps at its own
    // width (`u8 + u8`, `int * int`), as the native back end's `canonicalize` and the evaluator
    // compute it. Nothing for a word.
    canonical &self x:String k:Lit -> String {
        w: long = widthOfKind(k);
        if (w >= 8 || isFloat(k)) { return x; }
        bits: String = intBits(w);
        n: String = self.fresh();
        self.put("  ");
        self.putString(n);
        self.put(" = trunc i64 ");
        self.putString(x);
        self.put(" to ");
        self.putString(intBits(w));
        self.line("");
        r: String = self.fresh();
        self.put("  ");
        self.putString(r);
        if (isUnsignedInt(k)) { self.put(" = zext "); } else { self.put(" = sext "); }
        self.putString(bits);
        self.put(" ");
        self.putString(n);
        self.line(" to i64");
        return r;
    }

    // ─── floats ──────────────────────────────────────────────────────────────
    // A float is its bits in the word every temp is: an f64's 64, an f32's 32 sign-extended. To
    // compute, the word becomes a `double` (or an `i32` and a `float`) and the result goes back.

    toFp &self x:String single:bool -> String {
        if (!single) {
            f: String = self.fresh();
            self.put("  ");
            self.putString(f);
            self.put(" = bitcast i64 ");
            self.putString(x);
            self.line(" to double");
            return f;
        }
        n: String = self.fresh();
        nIdx: long = self.nextVal - 1;
        self.put("  ");
        self.putString(n);
        self.put(" = trunc i64 ");
        self.putString(x);
        self.line(" to i32");
        f: String = self.fresh();
        self.put("  ");
        self.putString(f);
        self.put(" = bitcast i32 %v");
        num: String;
        num.pushLong(nIdx);
        self.putString(num);
        self.line(" to float");
        return f;
    }

    fromFp &self f:String single:bool -> String {
        if (!single) {
            r: String = self.fresh();
            self.put("  ");
            self.putString(r);
            self.put(" = bitcast double ");
            self.putString(f);
            self.line(" to i64");
            return r;
        }
        n: String = self.fresh();
        nIdx: long = self.nextVal - 1;
        self.put("  ");
        self.putString(n);
        self.put(" = bitcast float ");
        self.putString(f);
        self.line(" to i32");
        r: String = self.fresh();
        self.put("  ");
        self.putString(r);
        self.put(" = sext i32 %v");
        num: String;
        num.pushLong(nIdx);
        self.putString(num);
        self.line(" to i64");
        return r;
    }

    floatBinary &self in:Instr mnemonic:str -> void {
        single: bool = in.kind == Lit.Float;
        x: String = self.toFp(self.operand(in, 0), single);
        y: String = self.toFp(self.operand(in, 1), single);
        r: String = self.fresh();
        self.put("  ");
        self.putString(r);
        self.put(" = ");
        self.put(mnemonic);
        if (single) { self.put(" float "); } else { self.put(" double "); }
        self.putString(x);
        self.put(", ");
        self.putString(y);
        self.line("");
        self.writeTemp(in.dst, self.fromFp(r, single));
    }

    // `fcmp` with an ordered predicate is false on a NaN, `une` true: the language's semantics.
    floatCmp &self in:Instr op:IROp -> String {
        single: bool = in.kind == Lit.Float;
        x: String = self.toFp(self.operand(in, 0), single);
        y: String = self.toFp(self.operand(in, 1), single);
        c: String = self.fresh();
        self.put("  ");
        self.putString(c);
        self.put(" = fcmp ");
        self.put(llvmFloatPred(op));
        if (single) { self.put(" float "); } else { self.put(" double "); }
        self.putString(x);
        self.put(", ");
        self.putString(y);
        self.line("");
        return c;
    }

    floatCompare &self in:Instr -> void {
        c: String = self.floatCmp(in, in.op);
        w: String = self.fresh();
        self.put("  ");
        self.putString(w);
        self.put(" = zext i1 ");
        self.putString(c);
        self.line(" to i64");
        self.writeTemp(in.dst, w);
    }

    // A conversion with a float on at least one side.
    floatConvert &self in:Instr -> void {
        from: Lit = in.fromKind;
        to: Lit = in.toKind;
        x: String = self.readTemp(in.a);
        if (from == to) { self.writeTemp(in.dst, x); return; }
        if (isFloat(from) && isFloat(to)) {
            f: String = self.toFp(x, from == Lit.Float);
            r: String = self.fresh();
            self.put("  ");
            self.putString(r);
            if (from == Lit.Float) { self.put(" = fpext float "); } else { self.put(" = fptrunc double "); }
            self.putString(f);
            if (to == Lit.Float) { self.line(" to float"); } else { self.line(" to double"); }
            self.writeTemp(in.dst, self.fromFp(r, to == Lit.Float));
            return;
        }
        if (isFloat(to)) {
            r: String = self.fresh();
            self.put("  ");
            self.putString(r);
            if (from == Lit.U64) { self.put(" = uitofp i64 "); } else { self.put(" = sitofp i64 "); }
            self.putString(x);
            if (to == Lit.Float) { self.line(" to float"); } else { self.line(" to double"); }
            self.writeTemp(in.dst, self.fromFp(r, to == Lit.Float));
            return;
        }
        // A float to an integer: toward zero, to a word, then the integer's canonical form.
        f: String = self.toFp(x, from == Lit.Float);
        r: String = self.fresh();
        rIdx: long = self.nextVal - 1;
        self.put("  ");
        self.putString(r);
        if (to == Lit.U64) { self.put(" = fptoui "); } else { self.put(" = fptosi "); }
        if (from == Lit.Float) { self.put("float "); } else { self.put("double "); }
        self.putString(f);
        self.line(" to i64");
        w: long = typeInfo(to).size;
        word: String;
        word.pushStr("%v");
        word.pushLong(rIdx);
        if (w < 1 || w >= 8) { self.writeTemp(in.dst, word); return; }
        bits: String;
        bits.pushStr("i");
        bits.pushLong(w * 8);
        bitsIdx: String;
        bitsIdx.pushStr("i");
        bitsIdx.pushLong(w * 8);
        n: String = self.fresh();
        self.put("  ");
        self.putString(n);
        self.put(" = trunc i64 ");
        self.putString(word);
        self.put(" to ");
        self.putString(bits);
        self.line("");
        q: String = self.fresh();
        self.put("  ");
        self.putString(q);
        if (isUnsignedInt(to)) { self.put(" = zext "); } else { self.put(" = sext "); }
        self.putString(bitsIdx);
        self.put(" ");
        self.putString(n);
        self.line(" to i64");
        self.writeTemp(in.dst, q);
    }

    // A comparison is `i1` in LLVM and 0 or 1 in this IR, so it is widened back to a word.
    compare &self in:Instr pred:str -> void {
        x: String = self.operand(in, 0);
        y: String = self.operand(in, 1);
        c: String = self.fresh();
        self.put("  ");
        self.putString(c);
        self.put(" = icmp ");
        self.put(pred);
        self.put(" i64 ");
        self.putString(x);
        self.put(", ");
        self.putString(y);
        self.line("");
        w: String = self.fresh();
        self.put("  ");
        self.putString(w);
        self.put(" = zext i1 ");
        self.putString(c);
        self.line(" to i64");
        self.writeTemp(in.dst, w);
    }

    // An address is a plain i64 in this IR, the way `&x` is a raw 64-bit address in the language.
    // LLVM needs a `ptr` to load through, so one is formed at each site and the offset applied in
    // bytes: `getelementptr i8` is byte arithmetic and needs no element type to be invented.
    addrAt &self a:String off:long -> String {
        p: String = self.fresh();
        self.put("  ");
        self.putString(p);
        self.put(" = inttoptr i64 ");
        self.putString(a);
        self.line(" to ptr");
        if (off == 0) { return p; }
        q: String = self.fresh();
        self.put("  ");
        self.putString(q);
        self.put(" = getelementptr i8, ptr ");
        self.putString(p);
        self.put(", i64 ");
        s: String;
        s.pushLong(off);
        self.putString(s);
        self.line("");
        return q;
    }
    // A pointer back to the i64 the IR keeps addresses in.
    addrOfPtr &self ptr:String -> String {
        v: String = self.fresh();
        self.put("  ");
        self.putString(v);
        self.put(" = ptrtoint ptr ");
        self.putString(ptr);
        self.line(" to i64");
        return v;
    }

    // One `alloca` per scratch slot however many times the body names it: repeating the
    // definition is not a duplicate store, it is invalid IR.
    seenAgg &self i:long -> bool {
        key: String;
        key.pushStr("agg#");
        key.pushLong(i);
        k: str = "";
        unsafe { k = key.view(); }
        if (self.slots.has(k)) { return true; }
        self.slots.put(keepString(key), true);
        return false;
    }

    // The `alloca` holding hidden aggregate scratch slot `i`.
    aggSlotName &self i:long -> String {
        s: String;
        s.pushStr("%agg");
        s.pushLong(i);
        return s;
    }

    // `@gbl_...`, the symbol a file global is emitted under.
    globalRef &self n:Sym -> String {
        s: String;
        s.pushStr("@\"");
        s.pushStr(globalSymbol(nameOf(n)));
        s.pushStr("\"");
        return s;
    }
    // A global is stored as bytes, so a read of one is a load at the width its kind names, the
    // same as any other load through a pointer.
    loadGlobal &self in:Instr -> String {
        w: long = widthOfKind(in.kind);
        bits: String = intBits(w);
        n: String = self.fresh();
        self.put("  ");
        self.putString(n);
        self.put(" = load ");
        self.putString(bits);
        self.put(", ptr ");
        self.putString(self.globalRef(in.name));
        self.line("");
        if (w == 8) { return n; }
        r: String = self.fresh();
        self.put("  ");
        self.putString(r);
        if (isUnsignedInt(in.kind)) { self.put(" = zext "); } else { self.put(" = sext "); }
        self.putString(bits);
        self.put(" ");
        self.putString(n);
        self.line(" to i64");
        return r;
    }
    // The two widths are written out rather than sharing a `val` variable: `putString` takes its
    // String by value, so naming the same one on both paths is a move the checker refuses.
    storeGlobal &self in:Instr v:String -> void {
        w: long = widthOfKind(in.kind);
        if (w == 8) {
            self.put("  store i64 ");
            self.putString(v);
            self.put(", ptr ");
            self.putString(self.globalRef(in.name));
            self.line("");
            return;
        }
        // The value's number is kept rather than its text: `putString` moves, so the name cannot
        // be handed over twice.
        idx: long = self.nextVal;
        n: String = self.fresh();
        self.put("  ");
        self.putString(n);
        self.put(" = trunc i64 ");
        self.putString(v);
        self.put(" to ");
        self.putString(intBits(w));
        self.line("");
        self.put("  store ");
        self.putString(intBits(w));
        self.put(" %v");
        num: String;
        num.pushLong(idx);
        self.putString(num);
        self.put(", ptr ");
        self.putString(self.globalRef(in.name));
        self.line("");
    }

    // `alloca` for a named slot, once per function. Emitted in the entry block, which is where
    // `mem2reg` looks: an alloca anywhere else is legal and never promoted.
    // A slot is as big as the declaration said, not one word. A local array or a struct is
    // addressed through `&a` and written past the first element, so an `alloca i64` for one is
    // eight bytes of storage and a stack smash the moment `a[1]` is assigned.
    //
    // A word-sized slot stays `alloca i64` rather than `[8 x i8]`, because `mem2reg` promotes a
    // scalar alloca and leaves a byte array in memory: this is what keeps ordinary locals in
    // registers.
    declareSlot &self n:Sym bytes:long -> void {
        q: str = nameOf(n);
        if (self.slots.has(q)) { return; }
        self.slots.put(q, true);
        self.put("  ");
        self.putString(self.nameSlot(n));
        if (bytes <= 8) { self.line(" = alloca i64"); return; }
        self.put(" = alloca [");
        s: String;
        s.pushLong(bytes);
        self.putString(s);
        self.line(" x i8], align 8");
    }
}

// Does any `in`/`out` of this block bind `reg`? A bound register must not also be a clobber:
// LLVM refuses that outright.
local asmBinds p:IRProgram in:Instr reg:str -> bool {
    for k in 0..in.pieceCount {
        at: long = in.firstPiece + k;
        ak: AsmKind = p.asmKinds.get(at);
        if (ak != AsmKind.Text && nameOf(p.asmRegs.get(at)) == reg) { return true; }
    }
    return false;
}

// The sub-register a `{reg}` placeholder means: the one as wide as the value an `in` bound to it.
// The same rule as `Emitter::sizedReg`, where only an input decides.
local sizedRegOf p:IRProgram in:Instr want:str line:str -> str {
    for k in 0..in.pieceCount {
        at: long = in.firstPiece + k;
        if (p.asmKinds.get(at) == AsmKind.In && nameOf(p.asmRegs.get(at)) == want) {
            return regNameSized(regIndexOf(want), p.asmSizes.get(at));
        }
    }
    failStr(format("placeholder `{{{}}}` in an `asm` block names a register no `in` binds\nnote: the line is `{}`\nhelp: bind it with `in {} <value>`, or write the register without braces", want, line, want));
    return want;
}

// NASM and LLVM's Intel dialect disagree on four spellings: `[rel sym]` is RIP-relative, which
// LLVM writes `[rip + sym]`; `[fs:reg]` is a segment override, which LLVM writes with the segment
// outside the brackets as `fs:[reg]`; a memory operand's size is `dword [x]` in NASM and
// `dword ptr [x]` in LLVM, which reads the bare keyword as a symbol and refuses the line; and a
// `;` starts a comment in NASM, which LLVM's parser does not take, so the comment is dropped (not
// inside a quote, where it is a character).
local rewriteRel s:str -> String {
    out: String;
    i: long = 0;
    quote: long = 0;
    while (i < s.len) {
        c: long = charAt(s, i);
        if (quote != 0) {
            if (c == quote || c == '\n') { quote = 0; }
            out.push(c as char);
            i = i + 1;
            continue;
        }
        if (c == '\'' || c == '"') { quote = c; out.push(c as char); i = i + 1; continue; }
        if (c == ';') {
            while (i < s.len && charAt(s, i) != '\n') { i = i + 1; }
            continue;
        }
        sized: long = sizeKeywordAt(s, i);
        if (sized > 0) {
            out.pushStr(strSlice(s, i, sized));
            out.pushStr(" ptr");
            i = i + sized;
        } else if (i + 4 < s.len && charAt(s, i) == '[' && charAt(s, i + 1) == 'r'
            && charAt(s, i + 2) == 'e' && charAt(s, i + 3) == 'l' && charAt(s, i + 4) == ' ') {
            out.pushStr("[rip + ");
            i = i + 5;
        } else if (i + 3 < s.len && charAt(s, i) == '[' && charAt(s, i + 3) == ':'
                   && (charAt(s, i + 1) == 'f' || charAt(s, i + 1) == 'g')
                   && charAt(s, i + 2) == 's') {
            out.push(charAt(s, i + 1) as char);
            out.push('s');
            out.pushStr(":[");
            i = i + 4;
        } else {
            out.push(charAt(s, i) as char);
            i = i + 1;
        }
    }
    return out;
}

// The length of a NASM size keyword (`byte`, `word`, `dword`, `qword`, `tword`, `oword`) that
// starts a word at `i` and is followed by a memory operand without `ptr`, or 0.
local sizeKeywordAt s:str i:long -> long {
    if (i > 0 && (isIdentPart(charAt(s, i - 1)) || charAt(s, i - 1) == '.')) { return 0; }
    n: long = 0;
    if (strStartsWith(strSlice(s, i, s.len - i), "byte")) { n = 4; }
    else if (strStartsWith(strSlice(s, i, s.len - i), "word")) { n = 4; }
    else {
        c: long = 0;
        if (i < s.len) { c = charAt(s, i); }
        if ((c == 'd' || c == 'q' || c == 't' || c == 'o') && strStartsWith(strSlice(s, i + 1, s.len - i - 1), "word")) { n = 5; }
    }
    if (n == 0) { return 0; }
    j: long = i + n;
    if (j < s.len && charAt(s, j) != ' ' && charAt(s, j) != '[') { return 0; }
    while (j < s.len && charAt(s, j) == ' ') { j = j + 1; }
    if (j < s.len && charAt(s, j) == '[') { return n; }
    return 0;
}

local bodyView inout s:String -> str {
    v: str = "";
    unsafe { v = s.view(); }
    return v;
}


// One image: byte runs and, at each relocation offset, an eight-byte word naming what it points
// at. LLVM says that with a packed struct constant, so the type and the value are built together
// and `ptrtoint` carries the address a mention in code would have used.
local emitImageConst inout e:LlvmEmitter inout p:IRProgram im:long inout ty:String inout val:String -> void {
    first: long = p.imageFirst.get(im);
    count: long = p.imageCount.get(im);
    rf: long = p.imageRelocFirst.get(im);
    rc: long = p.imageRelocCount.get(im);
    at: long = 0;
    r: long = 0;
    firstMember: bool = true;
    while (at < count) {
        if (!firstMember) { ty.pushStr(", "); val.pushStr(", "); }
        firstMember = false;
        if (r < rc && p.relocOffset.get(rf + r) == at) {
            k: RelocKind = p.relocKind.get(rf + r);
            sym: String = relocSymbol(p, k, p.relocTarget.get(rf + r));
            d: long = p.relocDelta.get(rf + r);
            ty.pushStr("i64");
            if (d != 0) { val.pushStr("i64 add (i64 ptrtoint (ptr "); } else { val.pushStr("i64 ptrtoint (ptr "); }
            unsafe { val.pushStr(sym.view()); }
            val.pushStr(" to i64)");
            if (d != 0) { val.pushStr(", i64 "); val.pushLong(d); val.pushStr(")"); }
            at = at + 8;
            r = r + 1;
        } else {
            stopAt: long = count;
            if (r < rc) { stopAt = p.relocOffset.get(rf + r); }
            n: long = stopAt - at;
            ty.pushStr("[");
            ty.pushLong(n);
            ty.pushStr(" x i8]");
            val.pushStr("[");
            val.pushLong(n);
            val.pushStr(" x i8] c\"");
            for k in at..stopAt {
                pushByte(&val, p.imageBytes.get(first + k) as long);
            }
            val.pushStr("\"");
            at = stopAt;
        }
    }
    if (firstMember) { ty.pushStr("[0 x i8]"); val.pushStr("[0 x i8] zeroinitializer"); }
}

// The literals, the folded images and the file globals. Emitted whole: what the program does not
// reach, the linker drops.
local emitData inout e:LlvmEmitter inout p:IRProgram -> void {
    // Each string twice over, the bytes and the {ptr, len} pair a `str` value is.
    for i in 0..p.strings.len() {
        text: str = nameOf(p.strings.get(i));
        bytes: String;
        n: long = 0;
        j: long = 0;
        while (j < text.len) {
            c: long = charAt(text, j);
            if (c == 92 && j + 1 < text.len) { j = j + 1; c = escapeByte(charAt(text, j)); }
            pushByte(&bytes, c);
            n = n + 1;
            j = j + 1;
        }
        e.put("@strb.");
        s: String;
        s.pushLong(i);
        e.putString(s);
        e.put(" = private unnamed_addr constant [");
        sn: String;
        sn.pushLong(n);
        e.putString(sn);
        e.put(" x i8] c\"");
        e.putString(bytes);
        e.line("\"");
        e.put("@strc.");
        e.putString(s);
        e.put(" = private unnamed_addr constant <{ i64, i64 }> <{ i64 ptrtoint (ptr @strb.");
        e.putString(s);
        e.put(" to i64), i64 ");
        e.putString(sn);
        e.line(" }>");
    }

    // The images. One marked as a block is a heap block the compiler built. The allocator finds a
    // region's header by masking a pointer down to a 64 KiB boundary, and that header says the
    // region is static, so freeing a block inside it does nothing. Emitted as a bare global
    // instead, `free` would read whatever happened to precede it, and the program would die at
    // drop time after printing everything correctly.
    //
    // The native emitter packs several blocks into one region to save the padding. Here each gets
    // its own, which costs a great deal of address space but no file size, since the padding is
    // zero.
    for i in 0..p.imageFirst.len() {
        ty: String;
        val: String;
        emitImageConst(&e, p, i, &ty, &val);
        s: String;
        s.pushLong(i);
        if (p.imageIsBlock.get(i)) {
            e.put("@ctbr.");
            e.putString(s);
            // `dq 1000, 0`, little end first: the marker the allocator reads.
            e.put(" = internal global <{ [16 x i8], ");
            e.putString(ty);
            e.put(" }> <{ [16 x i8] c\"\\E8\\03\\00\\00\\00\\00\\00\\00\\00\\00\\00\\00\\00\\00\\00\\00\", ");
            e.putString(val);
            e.line(" }>, align 65536");
        } else {
            e.put("@ctb.");
            e.putString(s);
            e.put(" = internal global <{ ");
            e.putString(ty);
            e.put(" }> <{ ");
            e.putString(val);
            e.line(" }>");
        }
    }

    // The heap's central block. `heap.k` reaches it by name from an `asm` block, so the back end
    // has to define it, as the native emitter does. It has external linkage and is pinned with
    // `llvm.used`, because a reference from inside assembly text is invisible to LLVM: made
    // `internal`, it would be localised and leave the assembler an undefined symbol, and if
    // nothing marked it used, it would be dropped.
    e.line("@__heapCentral = global [1024 x i8] zeroinitializer");
    e.line("@llvm.used = appending global [1 x ptr] [ptr @__heapCentral], section \"llvm.metadata\"");

    // The file globals: a folded image, a scalar the evaluator computed, or zeroed storage.
    for i in 0..p.globals.len() {
        name: str = globalSymbol(nameOf(p.globals.get(i)));
        e.put("@\"");
        e.put(name);
        e.put("\" = internal global ");
        if (p.globalImage.get(i) >= 0) {
            ty: String;
            val: String;
            emitImageConst(&e, p, p.globalImage.get(i), &ty, &val);
            e.put("<{ ");
            e.putString(ty);
            e.put(" }> <{ ");
            e.putString(val);
            e.line(" }>");
        } else if (p.globalHasInit.get(i)) {
            // Written as bytes, little end first, so every global has one shape whatever its width
            // and a load through it reads at the width its own kind names.
            nb: long = p.globalBytes.get(i);
            if (nb < 1) { nb = 8; }
            v: long = p.globalInits.get(i);
            bytes: String;
            for k in 0..nb {
                pushByte(&bytes, v & 255);
                v = v >> 8;
            }
            e.put("[");
            sb: String;
            sb.pushLong(nb);
            e.putString(sb);
            e.put(" x i8] c\"");
            e.putString(bytes);
            e.line("\"");
        } else {
            nb: long = p.globalBytes.get(i);
            if (nb < 1) { nb = 8; }
            e.put("[");
            sb: String;
            sb.pushLong(nb);
            e.putString(sb);
            e.line(" x i8] zeroinitializer");
        }
    }
    e.line("");
}


// One table of method addresses per concrete implementation, in the trait's own method order,
// which is what a trait object's second word points at.
//
// Deduplicated by LABEL rather than by impl, the way the native emitter does it: two impls whose
// trait references differ only in how the instantiation is spelled mangle to the same table name,
// and defining it twice is as invalid here as it is in NASM.
local emitVtables inout e:LlvmEmitter -> void {
    done: HashMap<str, bool>;
    i: long = 0;
    while (i < gReg.implCount()) {
        im: TraitImplDef = gReg.implAt(i);
        // A template implements nothing: only the stamped instances have addresses.
        if (gReg.isGenericSym(im.structName)) { i = i + 1; continue; }
        at: long = gReg.findTraitSym(im.trait.name);
        if (at < 0) { i = i + 1; continue; }
        label: str = implVtableName(im);
        if (done.has(label)) { i = i + 1; continue; }
        done.put(label, true);
        td: TraitDef = gReg.traitDef(at);
        e.put("@\"");
        e.put(label);
        e.put("\" = internal constant [");
        n: long = td.methodCount;
        if (n == 0) { n = 1; }
        s: String;
        s.pushLong(n);
        e.putString(s);
        e.put(" x i64] [");
        for k in 0..td.methodCount {
            if (k > 0) { e.put(", "); }
            e.put("i64 ptrtoint (ptr @\"");
            e.put(nameOf(implMethodName(im, gReg.traitMethodAt(td, k).name)));
            e.put("\" to i64)");
        }
        if (td.methodCount == 0) { e.put("i64 0"); }
        e.line("]");
        i = i + 1;
    }
}

pub emitLlvm inout p:IRProgram inout out:String -> void {
    e: LlvmEmitter;
    e.line("; generated by kilnc --emit=llvm");
    e.line("target triple = \"x86_64-unknown-linux-gnu\"");
    e.line("declare void @llvm.memcpy.inline.p0.p0.i64(ptr, ptr, i64, i1)");
    e.line("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)");
    e.line("declare void @llvm.memset.inline.p0.i64(ptr, i8, i64, i1)");
    e.line("");
    // Our own entry point, because this runtime owns `fs:` and glibc keeps its TLS there too:
    // linked against libc, a program ran correctly, returned the right value, and then died in
    // `__call_tls_dtors` on the way out.
    //
    // This follows `Emitter::emitStart`. The call not to lose is `$globalInit`, which runs the
    // initializers the evaluator could not fold; without it a program dies before printing
    // anything, because that is where the io buffers are built.
    startName: Sym = NO_SYM;
    hasInit: bool = false;
    wantsArgs: bool = false;
    for si in 0..p.funcs.len() {
        fnm: str = nameOf(p.funcs.get(si).name);
        if (p.funcs.get(si).isMain) { startName = p.funcs.get(si).name; wantsArgs = p.funcs.get(si).wantsArgs; }
        if (fnm == "$globalInit") { hasInit = true; }
    }
    if (startName != NO_SYM) {
        // Written as module-level assembly, not as a function. The kernel enters `_start` with the
        // stack 16-byte aligned and no return address on it, which is not the entry a compiled
        // function is built for: LLVM lays the frame out eight bytes off, and while nothing
        // notices at -O0, at -O1 the first aligned spill faults. `Emitter` writes `_start` by hand
        // for the same reason, and this does too, aligning the stack before it calls anything.
        //
        // An LLVM string takes `\XX` hex escapes and nothing else, so a quote inside the assembly
        // is `\\22`; and module-level assembly substitutes no operands, so `$` stands for itself.
        e.line("module asm \".globl _start\"");
        e.line("module asm \"_start:\"");
        e.line("module asm \"  andq $-16, %rsp\"");
        // The `@init` hooks, before any startup initializer, as `Emitter.emitStart` runs them.
        for k in 0..gInitHooks.len() { llvmCall(&e, gInitHooks.get(k)); }
        if (hasInit) { e.line("module asm \"  callq \\22$globalInit\\22\""); }
        if (wantsArgs) { emitArgvSlice(&e); }
        e.put("module asm \"  callq \\22");
        e.put(nameOf(startName));
        e.line("\\22\"");
        if (gFiniHooks.len() > 0) {
            e.line("module asm \"  pushq %rax\"");
            e.line("module asm \"  pushq %rax\"");
            e.line("module asm \"  callq __kiln_fini\"");
            e.line("module asm \"  popq %rax\"");
            e.line("module asm \"  popq %rax\"");
        }
        e.line("module asm \"  movq %rax, %rdi\"");
        e.line("module asm \"  movq $60, %rax\"");
        e.line("module asm \"  syscall\"");
        // What `_start` and the `exit` builtin call: every `@fini` hook, the last module's first.
        e.line("module asm \".globl __kiln_fini\"");
        e.line("module asm \"__kiln_fini:\"");
        if (gFiniHooks.len() > 0) {
            e.line("module asm \"  pushq %rbx\"");
            k: long = gFiniHooks.len();
            while (k > 0) { k = k - 1; llvmCall(&e, gFiniHooks.get(k)); }
            e.line("module asm \"  popq %rbx\"");
        }
        e.line("module asm \"  retq\"");
        e.line("");
    }

    emitData(&e, p);
    emitVtables(&e);
    for f in 0..p.funcs.len() {
        emitFunc(&e, p, p.funcs.get(f));
    }
    if (e.needBounds) {
        // The `@spill` function the report calls first, when this module defines it.
        spill: Sym = NO_SYM;
        for f in 0..p.funcs.len() {
            if (gSpillFn != NO_SYM && p.funcs.get(f).name == gSpillFn) { spill = gSpillFn; }
        }
        emitBoundsFail(&e, spill);
    }
    emitMemFunctions(&e);
    out.pushString(e.out);
}

// `memcpy`, `memmove`, `memset` and `memcmp`, which LLVM may call from any module (a zeroed
// struct, a loop it recognizes as a fill) and which nothing else provides in a freestanding
// program. Weak, so a C library linked in wins; `no-builtins`, so LLVM does not turn these loops
// back into calls to themselves.
local emitMemFunctions inout e:LlvmEmitter -> void {
    e.line("define weak ptr @memset(ptr %d, i32 %c, i64 %n) #0 {");
    e.line("entry:");
    e.line("  %b = trunc i32 %c to i8");
    e.line("  br label %head");
    e.line("head:");
    e.line("  %i = phi i64 [ 0, %entry ], [ %i1, %body ]");
    e.line("  %done = icmp eq i64 %i, %n");
    e.line("  br i1 %done, label %out, label %body");
    e.line("body:");
    e.line("  %p = getelementptr i8, ptr %d, i64 %i");
    e.line("  store i8 %b, ptr %p");
    e.line("  %i1 = add i64 %i, 1");
    e.line("  br label %head");
    e.line("out:");
    e.line("  ret ptr %d");
    e.line("}");
    e.line("define weak ptr @memcpy(ptr %d, ptr %s, i64 %n) #0 {");
    e.line("entry:");
    e.line("  br label %head");
    e.line("head:");
    e.line("  %i = phi i64 [ 0, %entry ], [ %i1, %body ]");
    e.line("  %done = icmp eq i64 %i, %n");
    e.line("  br i1 %done, label %out, label %body");
    e.line("body:");
    e.line("  %sp = getelementptr i8, ptr %s, i64 %i");
    e.line("  %v = load i8, ptr %sp");
    e.line("  %dp = getelementptr i8, ptr %d, i64 %i");
    e.line("  store i8 %v, ptr %dp");
    e.line("  %i1 = add i64 %i, 1");
    e.line("  br label %head");
    e.line("out:");
    e.line("  ret ptr %d");
    e.line("}");
    // Forward when the destination is below the source, else from the end.
    e.line("define weak ptr @memmove(ptr %d, ptr %s, i64 %n) #0 {");
    e.line("entry:");
    e.line("  %below = icmp ult ptr %d, %s");
    e.line("  br i1 %below, label %fhead, label %bhead");
    e.line("fhead:");
    e.line("  %i = phi i64 [ 0, %entry ], [ %i1, %fbody ]");
    e.line("  %fdone = icmp eq i64 %i, %n");
    e.line("  br i1 %fdone, label %out, label %fbody");
    e.line("fbody:");
    e.line("  %fs = getelementptr i8, ptr %s, i64 %i");
    e.line("  %fv = load i8, ptr %fs");
    e.line("  %fd = getelementptr i8, ptr %d, i64 %i");
    e.line("  store i8 %fv, ptr %fd");
    e.line("  %i1 = add i64 %i, 1");
    e.line("  br label %fhead");
    e.line("bhead:");
    e.line("  %j = phi i64 [ %n, %entry ], [ %j1, %bbody ]");
    e.line("  %bdone = icmp eq i64 %j, 0");
    e.line("  br i1 %bdone, label %out, label %bbody");
    e.line("bbody:");
    e.line("  %j1 = sub i64 %j, 1");
    e.line("  %bs = getelementptr i8, ptr %s, i64 %j1");
    e.line("  %bv = load i8, ptr %bs");
    e.line("  %bd = getelementptr i8, ptr %d, i64 %j1");
    e.line("  store i8 %bv, ptr %bd");
    e.line("  br label %bhead");
    e.line("out:");
    e.line("  ret ptr %d");
    e.line("}");
    e.line("define weak i32 @memcmp(ptr %a, ptr %b, i64 %n) #0 {");
    e.line("entry:");
    e.line("  br label %head");
    e.line("head:");
    e.line("  %i = phi i64 [ 0, %entry ], [ %i1, %same ]");
    e.line("  %done = icmp eq i64 %i, %n");
    e.line("  br i1 %done, label %equal, label %body");
    e.line("body:");
    e.line("  %ap = getelementptr i8, ptr %a, i64 %i");
    e.line("  %av = load i8, ptr %ap");
    e.line("  %bp = getelementptr i8, ptr %b, i64 %i");
    e.line("  %bv = load i8, ptr %bp");
    e.line("  %eq = icmp eq i8 %av, %bv");
    e.line("  br i1 %eq, label %same, label %differ");
    e.line("same:");
    e.line("  %i1 = add i64 %i, 1");
    e.line("  br label %head");
    e.line("differ:");
    e.line("  %ax = zext i8 %av to i32");
    e.line("  %bx = zext i8 %bv to i32");
    e.line("  %r = sub i32 %ax, %bx");
    e.line("  ret i32 %r");
    e.line("equal:");
    e.line("  ret i32 0");
    e.line("}");
    e.line("attributes #0 = { noinline \"no-builtins\" }");
}

// A byte string constant, `@name = private unnamed_addr constant [n x i8] c"..."`.
local byteConst inout e:LlvmEmitter name:str text:str -> void {
    b: String;
    for i in 0..text.len { pushByte(&b, charAt(text, i)); }
    s: String;
    s.pushStr(name);
    s.pushStr(" = private unnamed_addr constant [");
    s.pushLong(text.len);
    s.pushStr(" x i8] c\"");
    e.putString(s);
    e.putString(b);
    e.line("\"");
}

// What a failed bounds check runs: the native report (`Emitter.emitFailReport`) in the same words,
// taken from `boundsText`, written to fd 2 with no allocation and no buffered sink, then exit 134.
// The checks call `@__kiln_bounds_fail(index, length, where, whereLength, kind)`, where `kind` is
// the check's `BOUNDS_*` kind and picks the report's head and middle. `spill`, the program's
// `@spill` function or NO_SYM, is called first and once, as the native report does.
local emitBoundsFail inout e:LlvmEmitter spill:Sym -> void {
    if (spill != NO_SYM) { e.line("@__kiln_spilled = internal global i8 0"); }
    byteConst(&e, "@bnd.head", boundsText("__methBndHead"));
    byteConst(&e, "@bnd.mid", boundsText("__methBndMid"));
    byteConst(&e, "@bnd.rhead", boundsText("__methRngHead"));
    byteConst(&e, "@bnd.shead", boundsText("__methStartHead"));
    byteConst(&e, "@bnd.omid", boundsText("__methOrdMid"));
    byteConst(&e, "@bnd.at", boundsText("__methBndAt"));
    byteConst(&e, "@bnd.nl", "\n");
    for i in 0..e.locs.len() {
        n: String;
        n.pushStr("@bndloc.");
        n.pushLong(i);
        byteConst(&e, bodyView(&n), nameOf(e.locs.get(i)));
    }
    e.line("define internal void @__kiln_bnd_put(ptr %p, i64 %n) noinline {");
    e.line("  %r = call i64 asm sideeffect \"syscall\", \"={rax},{rax},{rdi},{rsi},{rdx},~{rcx},~{r11},~{memory}\"(i64 1, i64 2, ptr %p, i64 %n)");
    e.line("  ret void");
    e.line("}");
    // Signed, as the native one prints it: a negative index is the usual mistake.
    e.line("define internal void @__kiln_bnd_num(i64 %v) noinline {");
    e.line("entry:");
    e.line("  %buf = alloca [32 x i8]");
    e.line("  %neg = icmp slt i64 %v, 0");
    e.line("  %mv = sub i64 0, %v");
    e.line("  %abs = select i1 %neg, i64 %mv, i64 %v");
    e.line("  br label %digit");
    e.line("digit:");
    e.line("  %x = phi i64 [ %abs, %entry ], [ %q, %digit ]");
    e.line("  %at = phi i64 [ 32, %entry ], [ %at1, %digit ]");
    e.line("  %q = udiv i64 %x, 10");
    e.line("  %r = urem i64 %x, 10");
    e.line("  %d = add i64 %r, 48");
    e.line("  %c = trunc i64 %d to i8");
    e.line("  %at1 = sub i64 %at, 1");
    e.line("  %cp = getelementptr [32 x i8], ptr %buf, i64 0, i64 %at1");
    e.line("  store i8 %c, ptr %cp");
    e.line("  %more = icmp ne i64 %q, 0");
    e.line("  br i1 %more, label %digit, label %sign");
    e.line("sign:");
    e.line("  %at2 = sub i64 %at1, 1");
    e.line("  br i1 %neg, label %minus, label %out");
    e.line("minus:");
    e.line("  %mp = getelementptr [32 x i8], ptr %buf, i64 0, i64 %at2");
    e.line("  store i8 45, ptr %mp");
    e.line("  br label %out");
    e.line("out:");
    e.line("  %start = phi i64 [ %at1, %sign ], [ %at2, %minus ]");
    e.line("  %sp = getelementptr [32 x i8], ptr %buf, i64 0, i64 %start");
    e.line("  %len = sub i64 32, %start");
    e.line("  call void @__kiln_bnd_put(ptr %sp, i64 %len)");
    e.line("  ret void");
    e.line("}");
    e.line("define internal void @__kiln_bounds_fail(i64 %i, i64 %n, ptr %loc, i64 %loclen, i64 %kind) noreturn cold noinline {");
    e.line("entry:");
    if (spill != NO_SYM) {
        e.line("  %spilled = load i8, ptr @__kiln_spilled");
        e.line("  %fresh = icmp eq i8 %spilled, 0");
        e.line("  br i1 %fresh, label %spill, label %report");
        e.line("spill:");
        e.line("  store i8 1, ptr @__kiln_spilled");
        e.put("  %sp = call i64 @");
        e.putString(quoted(nameOf(spill)));
        e.line("()");
        e.line("  br label %report");
        e.line("report:");
    }
    // The head: "index" for an index, "slice end" for an end, "slice start" for either start.
    e.line("  %isidx = icmp eq i64 %kind, 0");
    e.line("  %isend = icmp eq i64 %kind, 1");
    e.line("  %hs = select i1 %isend, ptr @bnd.rhead, ptr @bnd.shead");
    e.line("  %h = select i1 %isidx, ptr @bnd.head, ptr %hs");
    selectLen(&e, "%hls", "%isend", boundsText("__methRngHead").len, boundsText("__methStartHead").len);
    hl: String;
    hl.pushStr("  %hl = select i1 %isidx, i64 ");
    hl.pushLong(boundsText("__methBndHead").len);
    hl.pushStr(", i64 %hls");
    e.putString(hl);
    e.line("");
    e.line("  call void @__kiln_bnd_put(ptr %h, i64 %hl)");
    e.line("  call void @__kiln_bnd_num(i64 %i)");
    // The middle: "is past slice end" for a start after its end, "out of range for length" else.
    e.line("  %isord = icmp eq i64 %kind, 2");
    e.line("  %m = select i1 %isord, ptr @bnd.omid, ptr @bnd.mid");
    selectLen(&e, "%ml", "%isord", boundsText("__methOrdMid").len, boundsText("__methBndMid").len);
    e.line("  call void @__kiln_bnd_put(ptr %m, i64 %ml)");
    e.line("  call void @__kiln_bnd_num(i64 %n)");
    e.line("  %has = icmp ne i64 %loclen, 0");
    e.line("  br i1 %has, label %where, label %end");
    e.line("where:");
    s: String;
    s.pushStr("  call void @__kiln_bnd_put(ptr @bnd.at, i64 ");
    s.pushLong(boundsText("__methBndAt").len);
    s.push(')');
    e.putString(s);
    e.line("");
    e.line("  call void @__kiln_bnd_put(ptr %loc, i64 %loclen)");
    e.line("  br label %end");
    e.line("end:");
    e.line("  call void @__kiln_bnd_put(ptr @bnd.nl, i64 1)");
    e.line("  call void asm sideeffect \"syscall\", \"{rax},{rdi},~{rcx},~{r11},~{memory}\"(i64 60, i64 134)");
    e.line("  unreachable");
    e.line("}");
}

// `  <name> = select i1 <cond>, i64 <yes>, i64 <no>`: a length that depends on the wording.
local selectLen inout e:LlvmEmitter name:str cond:str yes:long no:long -> void {
    s: String;
    s.pushStr("  ");
    s.pushStr(name);
    s.pushStr(" = select i1 ");
    s.pushStr(cond);
    s.pushStr(", i64 ");
    s.pushLong(yes);
    s.pushStr(", i64 ");
    s.pushLong(no);
    e.putString(s);
    e.line("");
}

// `main args: ...str`: the OS argc/argv as a slice of `str` built on the stack, its address in rdi
// for `main`. `Emitter.emitArgvSlice` in AT&T syntax: argc at [rsp], the pointers above it.
local emitArgvSlice inout e:LlvmEmitter -> void {
    lines: Vec<str> = vec![
        "movq (%rsp), %rax", "leaq 8(%rsp), %rsi", "movq %rax, %rbx", "shlq $4, %rbx", "addq $16, %rbx",
        "subq %rbx, %rsp", "xorq %rcx, %rcx",
        ".Lkiln_args_build:", "cmpq %rax, %rcx", "jge .Lkiln_args_done", "movq (%rsi,%rcx,8), %rdx", "movq %rdx, %r8",
        ".Lkiln_args_len:", "cmpb $0, (%r8)", "je .Lkiln_args_len_done", "incq %r8", "jmp .Lkiln_args_len",
        ".Lkiln_args_len_done:", "subq %rdx, %r8", "movq %rcx, %r9", "shlq $4, %r9", "movq %rdx, (%rsp,%r9)",
        "movq %r8, 8(%rsp,%r9)", "incq %rcx", "jmp .Lkiln_args_build",
        ".Lkiln_args_done:", "movq %rax, %r9", "shlq $4, %r9", "leaq (%rsp,%r9), %r10", "movq %rsp, (%r10)",
        "movq %rax, 8(%r10)", "movq %r10, %rdi"];
    for l in lines {
        e.put("module asm \"  ");
        e.put(l);
        e.line("\"");
    }
}

// `callq "<name>"` in module-level assembly: a hook `_start` calls.
local llvmCall inout e:LlvmEmitter n:Sym -> void {
    e.put("module asm \"  callq \\22");
    e.put(nameOf(n));
    e.line("\\22\"");
}

// How many parameters a function takes: the leading run of `paramSeed` loads, which is how the
// native emitter counts them too. Their order is the argument order and their names are the slots
// the body reads.
local paramCountOf p:IRProgram fn:IRFunc -> long {
    n: long = 0;
    while (n < fn.instrCount) {
        in: Instr = p.code.get(fn.firstInstr + n);
        if (in.op != IROp.Load || !in.paramSeed) { return n; }
        n = n + 1;
    }
    return n;
}

local emitFunc inout e:LlvmEmitter inout p:IRProgram fn:IRFunc -> void {
    e.closed = false;
    e.slots.clear();
    nparams: long = paramCountOf(p, fn);

    // A function holding an `asm` block is never inlined. The text may define a label, and
    // `thread.k` does (`.tcloneParent`); inlining the function around it emits that label twice
    // and the assembler refuses the second. The native back end cannot hit this because it emits
    // each block exactly once.
    hasAsm: bool = false;
    for ai in 0..fn.instrCount {
        if (p.code.get(fn.firstInstr + ai).op == IROp.Asm) { hasAsm = true; }
    }
    e.put("define i64 @");
    e.putString(quoted(nameOf(fn.name)));
    e.put("(");
    for k in 0..nparams {
        if (k > 0) { e.put(", "); }
        e.put("i64 %p");
        s: String;
        s.pushLong(k);
        e.putString(s);
    }
    if (hasAsm) { e.line(") noinline {"); } else { e.line(") {"); }
    e.line("entry:");

    // A slot per temp of this function...
    for t in fn.firstTemp..fn.tempCount {
        e.put("  ");
        e.putString(e.tempSlot(t));
        e.line(" = alloca i64");
    }
    // ...and one per named variable it touches, found up front so every alloca is in the entry
    // block where `mem2reg` will look for it.
    for k in 0..fn.instrCount {
        in: Instr = p.code.get(fn.firstInstr + k);
        if (!in.isGlobal && in.name != NO_SYM
            && (in.op == IROp.Load || in.op == IROp.Store || in.op == IROp.AddrOf)) {
            e.declareSlot(in.name, p.slotBytesOf(in.name));
        }
        // An `asm` block's `out` writes a slot by name and may be the only mention of it.
        if (in.op == IROp.Asm) {
            for j in 0..in.pieceCount {
                at: long = in.firstPiece + j;
                if (p.asmKinds.get(at) == AsmKind.Out && p.asmNames.get(at) != NO_SYM) {
                    e.declareSlot(p.asmNames.get(at), p.slotBytesOf(p.asmNames.get(at)));
                }
            }
        }
    }
    // ...and one per hidden aggregate scratch slot this body uses, sized as the program recorded.
    for k in 0..fn.instrCount {
        in: Instr = p.code.get(fn.firstInstr + k);
        if (in.op == IROp.AggSlot && !e.seenAgg(in.imm)) {
            e.put("  ");
            e.putString(e.aggSlotName(in.imm));
            e.put(" = alloca [");
            s: String;
            s.pushLong(p.aggSlots.get(in.imm));
            e.putString(s);
            e.line(" x i8], align 8");
        }
    }

    // The arguments into their slots, the way the native prologue drains the argument registers.
    for k in 0..nparams {
        in: Instr = p.code.get(fn.firstInstr + k);
        e.declareSlot(in.name, p.slotBytesOf(in.name));
        s: String;
        s.pushLong(k);
        // A by-value aggregate arrives as a pointer to the caller's copy, and the prologue copies
        // it into storage of its own, which lets the body write the parameter without writing the
        // caller's object. The body reads it out of the slot with `addrof self`, so a slot holding
        // the pointer instead of the bytes would read a struct out of an address. The seed
        // carries the byte count in `imm`, and `byValueAggregate` is the same test the native
        // prologue makes.
        if (byValueAggregate(in.kind)) {
            pp: String = e.fresh();
            e.put("  ");
            e.putString(pp);
            e.put(" = inttoptr i64 %p");
            e.putString(s);
            e.line(" to ptr");
            e.put("  call void @llvm.memcpy.inline.p0.p0.i64(ptr ");
            e.putString(e.nameSlot(in.name));
            e.put(", ptr ");
            e.putString(pp);
            e.put(", i64 ");
            sb: String;
            sb.pushLong(in.imm);
            e.putString(sb);
            e.line(", i1 false)");
        } else {
            e.put("  store i64 %p");
            e.putString(s);
            e.put(", ptr ");
            e.putString(e.nameSlot(in.name));
            e.line("");
        }
    }

    // The body, past the seeds: the prologue above has already stored them.
    e.fnFirst = fn.firstInstr;
    e.fnCount = fn.instrCount;
    for k in nparams..fn.instrCount {
        emitInstr(&e, p, p.code.get(fn.firstInstr + k));
    }
    if (!e.closed) { e.line("  ret i64 0"); }
    e.line("}");
    e.line("");
}

local emitInstr inout e:LlvmEmitter inout p:IRProgram in:Instr -> void {
    if (in.op == IROp.Nop) { return; }
    // A `raise` resumes at an address the record holds, with the stack and registers it saved,
    // which LLVM cannot be told about.
    if (in.op == IROp.RecoverPush || in.op == IROp.FaultEdge) { unsupported("a `recover` statement"); return; }

    if (in.op == IROp.Const) {
        s: String;
        s.pushLong(in.imm);
        e.writeTemp(in.dst, s);
        return;
    }
    if (in.op == IROp.Mov) { e.writeTemp(in.dst, e.readTemp(in.a)); return; }

    if (in.op == IROp.Load) {
        if (in.isGlobal) { e.writeTemp(in.dst, e.loadGlobal(in)); return; }
        v: String = e.fresh();
        e.put("  ");
        e.putString(v);
        e.put(" = load i64, ptr ");
        e.putString(e.nameSlot(in.name));
        e.line("");
        e.writeTemp(in.dst, v);
        return;
    }
    if (in.op == IROp.Store) {
        if (in.isGlobal) { e.storeGlobal(in, e.readTemp(in.a)); return; }
        v: String = e.readTemp(in.a);
        // A slot is an `i64`, so a value that need not be one of the variable's (an `int` in a
        // `u8`: a declaration takes any integer) is narrowed to it here, as the native store
        // narrows by its width (`narrowsInto`).
        if (narrowsInto(p.kindOf(in.a), in.kind)) { v = e.canonical(v, in.kind); }
        e.put("  store i64 ");
        e.putString(v);
        e.put(", ptr ");
        e.putString(e.nameSlot(in.name));
        e.line("");
        return;
    }

    if (isFloat(in.kind)) {
        if (in.op == IROp.Add) { e.floatBinary(in, "fadd"); return; }
        if (in.op == IROp.Sub) { e.floatBinary(in, "fsub"); return; }
        if (in.op == IROp.Mul) { e.floatBinary(in, "fmul"); return; }
        if (in.op == IROp.Div) { e.floatBinary(in, "fdiv"); return; }
        if (isCompare(in.op)) { e.floatCompare(in); return; }
    }
    if (in.op == IROp.Convert && (isFloat(in.fromKind) || isFloat(in.toKind))) { e.floatConvert(in); return; }
    if (in.op == IROp.Add)  { e.binary(in, "add");  return; }
    if (in.op == IROp.Sub)  { e.binary(in, "sub");  return; }
    if (in.op == IROp.Mul)  { e.binary(in, "mul");  return; }
    uns: bool = typeInfo(in.kind).unsignedNum;
    if (in.op == IROp.Div)  { if (uns) { e.binary(in, "udiv"); } else { e.binary(in, "sdiv"); } return; }
    if (in.op == IROp.Mod)  { if (uns) { e.binary(in, "urem"); } else { e.binary(in, "srem"); } return; }
    if (in.op == IROp.BAnd) { e.binary(in, "and");  return; }
    if (in.op == IROp.BOr)  { e.binary(in, "or");   return; }
    if (in.op == IROp.BXor) { e.binary(in, "xor");  return; }
    if (in.op == IROp.Shl)  { e.binary(in, "shl");  return; }
    if (in.op == IROp.Shr)  { if (uns) { e.binary(in, "lshr"); } else { e.binary(in, "ashr"); } return; }

    if (in.op == IROp.BNot) {
        x: String = e.readTemp(in.a);
        r: String = e.fresh();
        e.put("  ");
        e.putString(r);
        e.put(" = xor i64 ");
        e.putString(x);
        e.line(", -1");
        e.writeTemp(in.dst, e.canonical(r, in.kind));
        return;
    }

    if (in.op == IROp.CmpEq) { e.compare(in, "eq");  return; }
    if (in.op == IROp.CmpNe) { e.compare(in, "ne");  return; }
    if (in.op == IROp.CmpLt || in.op == IROp.CmpGt || in.op == IROp.CmpLe || in.op == IROp.CmpGe) {
        e.compare(in, llvmPred(in.op, uns));
        return;
    }

    // A convert is the canonical form of its target type: narrow to the target's width, then back
    // to a word the way a load of that type would, which is what makes `(-56) as u8` 200.
    if (in.op == IROp.Convert) {
        w: long = typeInfo(in.toKind).size;
        if (w < 1 || w > 8) { w = 8; }
        x: String = e.readTemp(in.a);
        if (w == 8) { e.writeTemp(in.dst, x); return; }
        bits: String;
        bits.pushStr("i");
        bits.pushLong(w * 8);
        n: String = e.fresh();
        e.put("  ");
        e.putString(n);
        e.put(" = trunc i64 ");
        e.putString(x);
        e.put(" to ");
        e.putString(bits);
        e.line("");
        r: String = e.fresh();
        e.put("  ");
        e.putString(r);
        if (isUnsignedInt(in.toKind)) { e.put(" = zext "); } else { e.put(" = sext "); }
        e.putString(bits);
        e.put(" ");
        e.putString(n);
        e.line(" to i64");
        e.writeTemp(in.dst, r);
        return;
    }

    if (in.op == IROp.RetVoid) { e.line("  ret i64 0"); e.closed = true; return; }
    if (in.op == IROp.Ret) {
        v: String = e.readTemp(in.a);
        e.put("  ret i64 ");
        e.putString(v);
        e.line("");
        e.closed = true;
        return;
    }

    if (in.op == IROp.Label) {
        // LLVM wants every block terminated, and this IR falls through between labels.
        if (!e.closed) {
            e.put("  br label ");
            e.putString(e.labelRef(in.name));
            e.line("");
        }
        e.putString(e.labelDef(in.name));
        e.line("");
        e.closed = false;
        return;
    }
    if (in.op == IROp.Jmp) {
        e.put("  br label ");
        e.putString(e.labelRef(in.name));
        e.line("");
        e.closed = true;
        return;
    }
    if (in.op == IROp.Jz) {
        x: String = e.readTemp(in.a);
        c: String = e.fresh();
        e.put("  ");
        e.putString(c);
        e.put(" = icmp eq i64 ");
        e.putString(x);
        e.line(", 0");
        // The block has to end here, so what follows gets a label of its own to fall into.
        fall: String = e.freshLabel();
        e.put("  br i1 ");
        e.putString(c);
        e.put(", label ");
        e.putString(e.labelRef(in.name));
        e.put(", label %\"");
        e.putString(fall);
        e.line("\"");
        e.put("\"");
        e.putString(fall);
        e.line("\":");
        e.closed = false;
        return;
    }

    if (in.op == IROp.Call) {
        // Each argument read makes exactly one value, so the k'th argument is `%v(first + k)` and
        // the names need not be kept. A `Vec<String>` could not be read back with `get` in any
        // case: a `String` owns its buffer, so `get` would be handing out a copy of one.
        first: long = e.nextVal;
        for k in 0..in.argCount {
            e.readTemp(p.args.get(in.firstArg + k));
        }
        // Named whether or not it is used: a call returning nothing is still a statement, and
        // leaving this unassigned on that path is what definite initialization refuses, correctly.
        r: String = e.fresh();
        e.put("  ");
        if (in.dst != NO_TEMP) {
            e.putString(r);
            e.put(" = ");
        }
        e.put("call i64 @");
        e.putString(quoted(nameOf(in.name)));
        e.put("(");
        for k in 0..in.argCount {
            if (k > 0) { e.put(", "); }
            e.put("i64 %v");
            s: String;
            s.pushLong(first + k);
            e.putString(s);
        }
        e.line(")");
        if (in.dst != NO_TEMP) { e.writeTemp(in.dst, r); }
        return;
    }

    // `(*a)(args...)`: the target is an address in a temp, which is what a fn value and a vtable
    // slot both hold. With opaque pointers the call names its own signature, so nothing has to be
    // reconstructed from the callee.
    if (in.op == IROp.CallIndirect) {
        target: String = e.readTemp(in.a);
        first: long = e.nextVal;
        for k in 0..in.argCount {
            e.readTemp(p.args.get(in.firstArg + k));
        }
        fp: String = e.fresh();
        e.put("  ");
        e.putString(fp);
        e.put(" = inttoptr i64 ");
        e.putString(target);
        e.line(" to ptr");
        r: String = e.fresh();
        e.put("  ");
        if (in.dst != NO_TEMP) {
            e.putString(r);
            e.put(" = ");
        }
        e.put("call i64 ");
        e.putString(fp);
        e.put("(");
        for k in 0..in.argCount {
            if (k > 0) { e.put(", "); }
            e.put("i64 %v");
            an: String;
            an.pushLong(first + k);
            e.putString(an);
        }
        e.line(")");
        if (in.dst != NO_TEMP) { e.writeTemp(in.dst, r); }
        return;
    }
    // An `asm` block. The pieces are `Text` verbatim, `In` binding a temp to a named register and
    // `Out` moving a register into a named slot afterwards; LLVM says the same with a constraint
    // string, outputs first and marked with `=`.
    //
    // `inteldialect` because this language writes Intel syntax (`mov rax, 60`) and LLVM inline
    // assembly is AT&T unless told otherwise. Without it the operands come out reversed, which
    // assembles cleanly and does the wrong thing.
    if (in.op == IROp.Asm) {
        nOut: long = 0;
        for k in 0..in.pieceCount {
            if (p.asmKinds.get(in.firstPiece + k) == AsmKind.Out) { nOut = nOut + 1; }
        }
        if (nOut > 1) { unsupported("an `asm` block with more than one `out`"); return; }

        first: long = e.nextVal;
        nIn: long = 0;
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) == AsmKind.In) {
                e.readTemp(p.asmVals.get(at));
                nIn = nIn + 1;
            }
        }

        body: String;
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) == AsmKind.Text) {
                if (body.length() > 0) { body.push('\n'); }
                line: str = nameOf(p.asmText.get(at));
                i: long = 0;
                while (i < line.len) {
                    c: long = charAt(line, i);
                    if (c != '{') { body.push(c as char); i = i + 1; }
                    else {
                        close: long = i + 1;
                        while (close < line.len && charAt(line, close) != '}') { close = close + 1; }
                        if (close >= line.len) { failStr(format("unclosed register placeholder in an `asm` block\nnote: the line is `{}`\nhelp: a placeholder is a register name in braces, such as `{{rax}}`", line)); }
                        want: str = strSlice(line, i + 1, close - i - 1);
                        body.pushStr(sizedRegOf(p, in, want, line));
                        i = close + 1;
                    }
                }
            }
        }

        // `[rel sym]` is how NASM spells RIP-relative; LLVM's Intel dialect spells the same thing
        // `[rip + sym]`, and reads `rel` as an unknown token. `heap.k` reaches `__heapCentral`
        // that way.
        fixed: String = rewriteRel(bodyView(&body));

        r: String = e.fresh();
        e.put("  ");
        if (nOut == 1) {
            e.putString(r);
            e.put(" = call i64 asm sideeffect inteldialect \"");
        } else {
            e.put("call void asm sideeffect inteldialect \"");
        }
        e.putString(escapeAsm(bodyView(&fixed)));
        e.put("\", \"");

        wrote: bool = false;
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) == AsmKind.Out) {
                e.put("={");
                e.put(nameOf(p.asmRegs.get(at)));
                e.put("}");
                wrote = true;
            }
        }
        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) == AsmKind.In) {
                if (wrote) { e.put(","); }
                e.put("{");
                e.put(nameOf(p.asmRegs.get(at)));
                e.put("}");
                wrote = true;
            }
        }
        for k in 0..9 {
            reg: str = callerSavedName(k);
            if (!asmBinds(p, in, reg)) {
                if (wrote) { e.put(","); }
                e.put("~{");
                e.put(reg);
                e.put("}");
                wrote = true;
            }
        }
        if (wrote) { e.put(","); }
        e.put("~{memory},~{dirflag},~{fpsr},~{flags}");
        e.put("\"(");
        for k in 0..nIn {
            if (k > 0) { e.put(", "); }
            e.put("i64 %v");
            s: String;
            s.pushLong(first + k);
            e.putString(s);
        }
        e.line(")");

        for k in 0..in.pieceCount {
            at: long = in.firstPiece + k;
            if (p.asmKinds.get(at) == AsmKind.Out) {
                // The one output gone to a promoted local's temp (`Opt.promoteLocals`).
                if (p.asmNames.get(at) == NO_SYM) { e.writeTemp(in.dst, r); continue; }
                // A slot holds its integer's canonical word, which the register need not
                // (`lock xadd [rbx], ax` leaves what was above `ax`): extended from the local's
                // width first, as its loads and stores say its type is.
                nk: Lit = Lit.Void;
                for q in 0..e.fnCount {
                    qi: long = e.fnFirst + q;
                    qo: IROp = p.code[qi].op;
                    if ((qo == IROp.Load || qo == IROp.Store) && !p.code[qi].isGlobal && p.code[qi].name == p.asmNames.get(at)) {
                        nk = p.code[qi].kind;
                        break;
                    }
                }
                v: String = r.clone();
                if (nk != Lit.Void) { v = e.canonical(r.clone(), nk); }
                e.put("  store i64 ");
                e.putString(v);
                e.put(", ptr ");
                e.putString(e.nameSlot(p.asmNames.get(at)));
                e.line("");
            }
        }
        return;
    }
    // `&x`: the address of a frame slot, as the i64 this IR keeps addresses in.
    if (in.op == IROp.AddrOf) {
        if (in.isGlobal) { e.writeTemp(in.dst, e.addrOfPtr(e.globalRef(in.name))); return; }
        e.writeTemp(in.dst, e.addrOfPtr(e.nameSlot(in.name)));
        return;
    }

    // A load through a pointer, at the width its kind names and extended back to a word the way
    // the native emitter's sized load does.
    // A load or store through an address may be through a raw pointer, which need not be aligned
    // (`bytes.k` reads a word at any byte, `hash128.k` too): `align 1`, which LLVM would
    // otherwise take as the type's own. On x86 the instructions are the same either way.
    if (in.op == IROp.PtrLoad) {
        a: String = e.readTemp(in.a);
        ptr: String = e.addrAt(a, in.imm);
        w: long = widthOfKind(in.kind);
        if (w == 8) {
            v: String = e.fresh();
            e.put("  ");
            e.putString(v);
            e.put(" = load i64, ptr ");
            e.putString(ptr);
            e.line(", align 1");
            e.writeTemp(in.dst, v);
            return;
        }
        bits: String = intBits(w);
        n: String = e.fresh();
        e.put("  ");
        e.putString(n);
        e.put(" = load ");
        e.putString(bits);
        e.put(", ptr ");
        e.putString(ptr);
        e.line(", align 1");
        r: String = e.fresh();
        e.put("  ");
        e.putString(r);
        if (isUnsignedInt(in.kind)) { e.put(" = zext "); } else { e.put(" = sext "); }
        e.putString(bits);
        e.put(" ");
        e.putString(n);
        e.line(" to i64");
        e.writeTemp(in.dst, r);
        return;
    }

    if (in.op == IROp.PtrStore) {
        a: String = e.readTemp(in.a);
        v: String = e.readTemp(in.b);
        ptr: String = e.addrAt(a, in.imm);
        w: long = widthOfKind(in.kind);
        if (w == 8) {
            e.put("  store i64 ");
            e.putString(v);
            e.put(", ptr ");
            e.putString(ptr);
            e.line(", align 1");
            return;
        }
        bits: String = intBits(w);
        n: String = e.fresh();
        e.put("  ");
        e.putString(n);
        e.put(" = trunc i64 ");
        e.putString(v);
        e.put(" to ");
        e.putString(bits);
        e.line("");
        e.put("  store ");
        e.putString(bits);
        e.put(" ");
        e.putString(n);
        e.put(", ptr ");
        e.putString(ptr);
        e.line(", align 1");
        return;
    }

    // An atomic, with the ordering its builtin names: an acquire load, a release store, and a
    // sequentially consistent store, swap, compare-and-swap and add. Narrow words are widened back
    // to a word the way the native emitter's sized load does.
    if (in.op == IROp.Atomic) {
        a: String = e.readTemp(in.a);
        ptr: String = e.addrAt(a, 0);
        w: long = widthOfKind(in.kind);
        bits: String = intBits(w);
        op: long = in.imm;
        val: String;
        if (in.b != NO_TEMP) { val = e.narrowTo(e.readTemp(in.b), w); }
        old: String;
        if (op == BI_ATOMIC_LOAD) {
            old = e.fresh();
            e.put("  "); e.putString(old); e.put(" = load atomic "); e.putString(bits); e.put(", ptr ");
            e.putString(ptr); e.put(" acquire, align "); e.putNum(w); e.line("");
        } else if (op == BI_ATOMIC_STORE || op == BI_ATOMIC_STORE_SC) {
            e.put("  store atomic "); e.putString(bits); e.put(" "); e.putString(val); e.put(", ptr "); e.putString(ptr);
            if (op == BI_ATOMIC_STORE) { e.put(" release"); } else { e.put(" seq_cst"); }
            e.put(", align "); e.putNum(w); e.line("");
            return;
        } else if (op == BI_ATOMIC_CAS) {
            want: String = e.narrowTo(e.readTemp(p.args.get(in.firstArg)), w);
            pair: String = e.fresh();
            e.put("  "); e.putString(pair); e.put(" = cmpxchg ptr "); e.putString(ptr); e.put(", ");
            e.putString(bits); e.put(" "); e.putString(val); e.put(", "); e.putString(bits); e.put(" ");
            e.putString(want); e.line(" seq_cst seq_cst");
            old = e.fresh();
            e.put("  "); e.putString(old); e.put(" = extractvalue { "); e.putString(bits); e.put(", i1 } ");
            e.putString(pair); e.line(", 0");
        } else {
            old = e.fresh();
            e.put("  "); e.putString(old); e.put(" = atomicrmw ");
            if (op == BI_ATOMIC_ADD) { e.put("add"); } else { e.put("xchg"); }
            e.put(" ptr "); e.putString(ptr); e.put(", "); e.putString(bits); e.put(" "); e.putString(val);
            e.line(" seq_cst");
        }
        if (in.dst == NO_TEMP) { return; }
        if (w == 8) { e.writeTemp(in.dst, old); return; }
        r: String = e.fresh();
        e.put("  "); e.putString(r);
        if (isUnsignedInt(in.kind)) { e.put(" = zext "); } else { e.put(" = sext "); }
        e.putString(bits); e.put(" "); e.putString(old); e.line(" to i64");
        e.writeTemp(in.dst, r);
        return;
    }

    // `memcpy [a] <- [b]`, which is what an aggregate assignment is.
    if (in.op == IROp.AggCopy) {
        a: String = e.readTemp(in.a);
        b: String = e.readTemp(in.b);
        dp: String = e.addrAt(a, 0);
        sp: String = e.addrAt(b, 0);
        e.put("  call void @llvm.memcpy.inline.p0.p0.i64(ptr ");
        e.putString(dp);
        e.put(", ptr ");
        e.putString(sp);
        e.put(", i64 ");
        s: String;
        s.pushLong(in.imm);
        e.putString(s);
        e.line(", i1 false)");
        return;
    }

    // `memcpy`: a length the program computes, so the intrinsic that may become a call.
    if (in.op == IROp.MemCopy) {
        a: String = e.readTemp(in.a);
        b: String = e.readTemp(in.b);
        n: String = e.readTemp(p.args.get(in.firstArg));
        dp: String = e.addrAt(a, 0);
        sp: String = e.addrAt(b, 0);
        e.put("  call void @llvm.memcpy.p0.p0.i64(ptr ");
        e.putString(dp);
        e.put(", ptr ");
        e.putString(sp);
        e.put(", i64 ");
        e.putString(n);
        e.line(", i1 false)");
        return;
    }

    // `memset [a] <- 0`: a local array declared without a value.
    if (in.op == IROp.AggZero) {
        a: String = e.readTemp(in.a);
        dp: String = e.addrAt(a, 0);
        e.put("  call void @llvm.memset.inline.p0.i64(ptr ");
        e.putString(dp);
        e.put(", i8 0, i64 ");
        s: String;
        s.pushLong(in.imm);
        e.putString(s);
        e.line(", i1 false)");
        return;
    }

    // The address of a hidden aggregate scratch slot. Its `alloca` was made at entry.
    if (in.op == IROp.AggSlot) {
        e.writeTemp(in.dst, e.addrOfPtr(e.aggSlotName(in.imm)));
        return;
    }

    // Trap unless the index is in range. A slice check (any kind but `BOUNDS_INDEX`) is inclusive.
    if (in.op == IROp.Bounds) {
        x: String = e.operand(in, 0);
        y: String = e.readTemp(in.b);
        c: String = e.fresh();
        e.put("  ");
        e.putString(c);
        if (in.imm != BOUNDS_INDEX) { e.put(" = icmp ule i64 "); } else { e.put(" = icmp ult i64 "); }
        e.putString(x);
        e.put(", ");
        e.putString(y);
        e.line("");
        okl: String = e.freshLabel();
        badl: String = e.freshLabel();
        e.put("  br i1 ");
        e.putString(c);
        e.put(", label %\"");
        e.putString(okl);
        e.put("\", label %\"");
        e.putString(badl);
        e.line("\"");
        e.put("\"");
        e.putString(badl);
        e.line("\":");
        // The native report: what was out of range, the length, where, then exit 134.
        e.needBounds = true;
        e.put("  call void @__kiln_bounds_fail(i64 ");
        e.putString(x);
        e.put(", i64 ");
        e.putString(y);
        if (in.name == NO_SYM) { e.put(", ptr null, i64 0"); }
        else {
            e.put(", ptr @bndloc.");
            s: String;
            s.pushLong(e.locIndex(in.name));
            s.pushStr(", i64 ");
            s.pushLong(nameOf(in.name).len);
            e.putString(s);
        }
        k: String;
        k.pushStr(", i64 ");
        k.pushLong(in.imm);
        k.pushStr(")");
        e.putString(k);
        e.line("");
        e.line("  unreachable");
        e.put("\"");
        e.putString(okl);
        e.line("\":");
        e.closed = false;
        return;
    }

    // The address of a function, which is what a fn value holds.
    if (in.op == IROp.FnAddr) {
        v: String = e.fresh();
        e.put("  ");
        e.putString(v);
        e.put(" = ptrtoint ptr @");
        e.putString(quoted(nameOf(in.name)));
        e.line(" to i64");
        e.writeTemp(in.dst, v);
        return;
    }

    if (in.op == IROp.ArrLoad || in.op == IROp.ArrStore) {
        unsupported("an array indexed by name"); return;
    }
    // The bytes of a literal, and the {ptr, len} pair a `str` value is.
    if (in.op == IROp.StrAddr || in.op == IROp.StrLitVal) {
        v: String = e.fresh();
        e.put("  ");
        e.putString(v);
        if (in.op == IROp.StrAddr) { e.put(" = ptrtoint ptr @strb."); } else { e.put(" = ptrtoint ptr @strc."); }
        s: String;
        s.pushLong(in.imm);
        e.putString(s);
        e.line(" to i64");
        e.writeTemp(in.dst, v);
        return;
    }
    // The address of a vtable, which is a trait object's second word.
    if (in.op == IROp.VtableAddr) {
        v: String = e.fresh();
        e.put("  ");
        e.putString(v);
        e.put(" = ptrtoint ptr @\"");
        e.put(nameOf(in.name));
        e.line("\" to i64");
        e.writeTemp(in.dst, v);
        return;
    }
    // A fused compare-and-branch. These do not come only from the optimizer:
    // `Lowerer::branchUnless` lowers a condition as one, so they arrive here with no optimizer in
    // the path at all.
    if (in.op == IROp.Jcc) {
        c: String;
        if (isFloat(in.kind)) { c = e.floatCmp(in, in.cmpOp); }
        else {
            x: String = e.operand(in, 0);
            y: String = e.operand(in, 1);
            c = e.fresh();
            cIdx: long = e.nextVal - 1;
            e.put("  %v");
            e.out.pushLong(cIdx);
            e.put(" = icmp ");
            e.put(llvmPred(in.cmpOp, typeInfo(in.kind).unsignedNum));
            e.put(" i64 ");
            e.putString(x);
            e.put(", ");
            e.putString(y);
            e.line("");
        }
        fall: String = e.freshLabel();
        e.put("  br i1 ");
        e.putString(c);
        e.put(", label ");
        e.putString(e.labelRef(in.name));
        e.put(", label %\"");
        e.putString(fall);
        e.line("\"");
        e.put("\"");
        e.putString(fall);
        e.line("\":");
        e.closed = false;
        return;
    }
    unsupported("this instruction");
}
